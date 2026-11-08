//! `linarith`: linear arithmetic at an ordered field, read at the field's
//! setoid equality (`docs/linarith-design.md`,
//! `issues/linarith-ordered-fields.md`).
//!
//! The tactic is an untrusted searcher in front of
//! `lib/std/tactic/linarith.hthr`. It reads the goal and the facts — the
//! written ones, then the context's — as `<`, `<=` and `≈` at one carrier
//! with `OrderedField` and `CommRingOfInt` instances (`Rat`, `CReal`), each side a linear
//! form over `ring`'s monomials (`crate::ring::FieldReading`), and looks for
//! a nonnegative combination of the facts and the goal's negation that is a
//! contradiction, by Fourier–Motzkin elimination. The certificate does not
//! replay the elimination: it states the combination directly,
//!
//! ```text
//! k·(b − a) ≈ Σ λᵢ·(hiᵢ − loᵢ) + c        (k, λᵢ positive, c ≥ 0)
//! ```
//!
//! proves the right side nonnegative (strictly, when a strict fact or `c`
//! is in it) from the library's part and sum lemmas, leaves the identity to
//! `ring`, and reads `a <= b` or `a < b` back with `lin_finish_le`/`_lt`.
//! When the goal's negation is not needed (`k = 0`) the facts alone are
//! contradictory and the goal follows from `lin_finish_false`. A reciprocal
//! whose denominator `d` a fact shows positive is cleared: every row that
//! mentions it is offered multiplied by `d` as well (`Factor`, `Use`), and
//! the goal's multiplier is then a positive term rather than a numeral
//! (design §5). Every step is checked through the class laws, so nothing
//! here decides an order, and a searcher bug can only make `linarith`
//! refuse or write a certificate the kernel rejects.
//!
//! At `Int` and `Nat` the search is `omega`'s (design §8,
//! `Elaborator::linarith_integral`): each side that multiplies is stated
//! equal to its normal form over monomials by `ring`, so `omega`, which reads
//! a product as an atom by its spelling, meets one monomial as one atom.

use std::collections::BTreeMap;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, Item, OpFixity, Span, parse_file};

use crate::context::Alias;
use crate::omega_cert::{local_facts, named_args, negated_domain};
use crate::relational_context::proof::Relation;
use crate::ring::{FieldReading, Linear};
use crate::statements::LetValue;
use crate::{Cx, ElabError, Elaborator, R};

type Z = i128;

/// The most rows an elimination may hold at once; past it the search gives
/// up rather than grow doubly exponentially.
const MAX_ROWS: usize = 2048;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rel {
    Le,
    Lt,
    Same,
}

/// `left R right` at a carrier.
struct Stated {
    rel: Rel,
    left: Rc<Term>,
    right: Rc<Term>,
    carrier: Rc<Type>,
    level: Level,
}

/// `ty` as the carrier's designated `≈`, `<` or `<=`, read as written; at a
/// class carrier, as its dictionary's (`ClassField`).
fn stated(elab: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Stated> {
    let relation = Relation::of_type(elab, cx, ty, span)?;
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let Some(carrier) = elab.carrier_of_ty(cx, &relation.carrier, span) else {
        let field = ClassField::of(elab, cx, &relation.carrier)?;
        let rel = [(&field.same, Rel::Same), (&field.lt, Rel::Lt), (&field.le, Rel::Le)]
            .into_iter()
            .find_map(|(op, rel)| (*relation.head == **op).then_some(rel))?;
        return Some(Stated {
            rel,
            left: relation.left,
            right: relation.right,
            carrier: relation.carrier,
            level: relation.level,
        });
    };
    [("≈", Rel::Same), ("<", Rel::Lt), ("<=", Rel::Le)].into_iter().find_map(|(sym, rel)| {
        let name = elab.designated(sym, OpFixity::Infix, &carrier.key)?;
        (named_args(elab, tm, &name)?.len() == 2).then(|| Stated {
            rel,
            left: Rc::clone(&relation.left),
            right: Rc::clone(&relation.right),
            carrier: Rc::clone(&relation.carrier),
            level: relation.level.clone(),
        })
    })
}

/// An ordered field that is a class carrier: a type parameter `K` whose
/// field is a dictionary in scope (`section<K: OrderedField(≈, <, <=, +,
/// *)>`), with no carrier instances. Its integers are the ones
/// every ring has, packaged by `ordered_field::OrderedField::with_ints<K>()`,
/// whose call's implicit arguments name `K`'s `≈`, `<`, `<=` as the section
/// binds them. The certificate gets the dictionary in scope
/// (`Elaborator::class_dictionary_scope`) and spells `K`'s constants and
/// negation through it (`Spell`).
#[derive(Clone)]
struct ClassField {
    ints: Rc<Term>,
    ty: Type,
    level: Level,
    same: Rc<Term>,
    lt: Rc<Term>,
    le: Rc<Term>,
}

/// The name a class carrier's ordered field dictionary is bound to.
const CLASS_FIELD: &str = "__lin_ints";

impl ClassField {
    fn of(elab: &Elaborator, cx: &Cx, carrier: &Type) -> Option<ClassField> {
        elab.scope_memo(cx, carrier, "linarith::ClassField", || ClassField::read(elab, cx, carrier))
    }

    fn read(elab: &Elaborator, cx: &Cx, carrier: &Type) -> Option<ClassField> {
        elab.key_of("ordered_field::OrderedField::with_ints")?;
        let source = elab.spell_type_clean(cx, carrier)?;
        let expr = parse_expr(&format!("ordered_field::OrderedField::with_ints<{source}>()")).ok()?;
        let (ints, ty, level) = elab.generated_scope(|me| me.elab_infer(cx, &expr)).ok()?;
        let (same, lt, le) = match named_args(elab, &ints, "ordered_field::OrderedField::with_ints")?.as_slice() {
            [_, same, lt, le, ..] => (Rc::clone(same), Rc::clone(lt), Rc::clone(le)),
            _ => return None,
        };
        Some(ClassField { ints: Rc::new(ints), ty, level, same, lt, le })
    }
}

/// How a certificate spells the carrier's constants and negation: numerals
/// and `-x` where the carrier designates them, and at a class carrier `K`
/// (`ClassField`) `K.unit`, `K.multiplicative.unit`, the integers' images
/// (`semiring::Ring::int_cast<K>(int::OfNat(2))`) and `K.inv(x)`, which
/// `ring` reads back as the same constants and negation.
struct Spell {
    class: Option<String>,
}

impl Spell {
    fn num(&self, k: Z) -> String {
        let Some(c) = &self.class else {
            return if k < 0 { format!("-{}", k.unsigned_abs()) } else { k.to_string() };
        };
        match k {
            0 => format!("{c}.unit"),
            1 => format!("{c}.multiplicative.unit"),
            k if k > 0 => format!("semiring::Ring::int_cast<{c}>(int::OfNat({k}))"),
            k => format!("semiring::Ring::int_cast<{c}>(int::NegSucc({}))", k.unsigned_abs() - 1),
        }
    }

    fn neg(&self, e: &str) -> String {
        match &self.class {
            None => format!("-{e}"),
            Some(c) => format!("{c}.inv({e})"),
        }
    }

    /// `hi + -lo`, as the lemmas state a difference.
    fn diff(&self, hi: &str, lo: &str) -> String {
        format!("({hi} + {})", self.neg(lo))
    }
}

/// What a fact or goal says, or its negation `¬(left < right)`.
enum Reading {
    Stated(Stated),
    NotLt(Stated),
}

impl Reading {
    /// A head β-redex is read through its contractum, as `omega` reads a
    /// fact (`spelling::beta_head_ty`): a pattern-bound `Exists` proof is
    /// typed by its predicate applied to the witness
    /// (issues/linarith-redex-typed-fact.md).
    fn of(elab: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Reading> {
        let contracted = crate::spelling::beta_head_ty(ty);
        let ty = contracted.as_ref().unwrap_or(ty);
        if let Some(s) = stated(elab, cx, ty, span) {
            return Some(Reading::Stated(s));
        }
        let domain = negated_domain(elab, cx, ty)?;
        let s = stated(elab, cx, &domain, span)?;
        (s.rel == Rel::Lt).then_some(Reading::NotLt(s))
    }

    fn stated(&self) -> &Stated {
        match self {
            Reading::Stated(s) | Reading::NotLt(s) => s,
        }
    }
}

/// A spelling with a class carrier's operator placeholders written back as
/// the operators they stand for: `#op+@0_3(a, b)` is `a + b`
/// (`traits::op_index_binder`), parenthesised by the surface's precedence;
/// with `carrier`, its dictionary placeholder `#constraint0` is the
/// carrier's name, as in `K.unit`
/// (issues/class-carrier-diagnostics-spell-placeholders.md).
fn resugar(spelled: &str, carrier: Option<&str>) -> String {
    fn prec(sym: &str) -> u8 {
        match sym {
            "*" | "/" | "%" => 7,
            "+" | "-" => 6,
            "<" | "<=" | "≈" | "=" | ">" | ">=" => 4,
            _ => 5,
        }
    }
    // A spelling with its placeholders written back, and the precedence of
    // its operator when the whole of it is one placeholder's application.
    fn walk(s: &str) -> (String, Option<u8>) {
        let mut out = String::new();
        let mut whole = None;
        let mut rest = s;
        while let Some(at) = rest.find("#op") {
            let after = &rest[at + 3..];
            let Some(open) = after.find('(') else { break };
            let Some(sym) = crate::traits::op_index_symbol(&rest[at..at + 3 + open]) else { break };
            let body = &after[open + 1..];
            // The balanced argument list, cut at its one top-level comma.
            let (mut depth, mut cuts, mut close) = (0usize, Vec::new(), None);
            for (i, c) in body.char_indices() {
                match c {
                    '(' | '[' => depth += 1,
                    ')' | ']' if depth == 0 => {
                        close = Some(i);
                        break;
                    }
                    ')' | ']' => depth -= 1,
                    ',' if depth == 0 => cuts.push(i),
                    _ => {}
                }
            }
            let (Some(close), &[cut]) = (close, cuts.as_slice()) else { break };
            let p = prec(sym);
            let (left, lp) = walk(body[..cut].trim());
            let (right, rp) = walk(body[cut + 1..close].trim());
            let left = if lp.is_some_and(|q| q < p) { format!("({left})") } else { left };
            let right = if rp.is_some_and(|q| q <= p) { format!("({right})") } else { right };
            whole = (out.is_empty() && at == 0 && body[close + 1..].is_empty()).then_some(p);
            out.push_str(&rest[..at]);
            out.push_str(&format!("{left} {sym} {right}"));
            rest = &body[close + 1..];
        }
        out.push_str(rest);
        (out, whole)
    }
    let (out, _) = walk(spelled);
    match carrier {
        Some(name) => {
            let mut fixed = String::new();
            let mut tail = out.as_str();
            while let Some(at) = tail.find("#constraint") {
                fixed.push_str(&tail[..at]);
                let digits = tail[at + 11..].chars().take_while(|c| c.is_ascii_digit()).count();
                fixed.push_str(name);
                tail = &tail[at + 11 + digits..];
            }
            fixed.push_str(tail);
            fixed
        }
        None => out,
    }
}

fn is_conjunction(elab: &Elaborator, ty: &Type) -> bool {
    elab.display_tag_of(ty).is_some_and(|ind| crate::goal_combinators::conjunction(&ind))
}

/// `ty` itself when it is a conjunction, or the first unfolding of its
/// head that is one (`AbsLe(z, e)` is `Within(<=, -e, z, e)`, which is
/// `-e <= z ∧ z <= e`), unless `ty` already reads as a relation
/// (docs/linarith-design.md §9).
fn conjunction_of(elab: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Type> {
    let contracted = crate::spelling::beta_head_ty(ty);
    let ty = contracted.as_ref().unwrap_or(ty);
    if is_conjunction(elab, ty) {
        return Some(ty.clone());
    }
    if Reading::of(elab, cx, ty, span).is_some() {
        return None;
    }
    crate::omega_cert::unfolded_proposition(elab, cx, ty, |t| is_conjunction(elab, t) || Reading::of(elab, cx, t, span).is_some())
        .filter(|t| is_conjunction(elab, t))
}

/// A fact's parts: the fact itself, or, when it is a conjunction or a
/// definition that unfolds to one (`conjunction_of`), each side through its
/// projection, recursively, named as the author would write it (`h.left`).
/// A part that is no relation is kept too; `add_fact` declines it.
#[allow(clippy::too_many_arguments)]
fn fact_parts(elab: &Elaborator, cx: &Cx, name: String, term: Term, ty: Type, level: Level, span: Span, out: &mut Vec<(String, Term, Type, Level)>) {
    if let Some(conj) = conjunction_of(elab, cx, &ty, span)
        && let Some(ind) = elab.display_tag_of(&conj)
    {
        let term = Rc::new(term);
        let sides: Option<Vec<_>> = ["left", "right"]
            .into_iter()
            .enumerate()
            .map(|(idx, field)| {
                elab.project_field(cx, &ind, &conj, Rc::clone(&term), idx, span)
                    .ok()
                    .map(|(side, side_ty, side_level)| (format!("{name}.{field}"), side, side_ty, side_level))
            })
            .collect();
        if let Some(sides) = sides {
            for (side_name, side, side_ty, side_level) in sides {
                fact_parts(elab, cx, side_name, side, side_ty, side_level, span, out);
            }
            return;
        }
        out.push((name, (*term).clone(), ty, level));
        return;
    }
    out.push((name, term, ty, level));
}

/// One row of the problem: `hi − lo ≥ 0` (or `> 0`), with the lemma that
/// proves it from its fact, applied to `args` and the fact.
#[derive(Clone)]
struct Row {
    lo: usize,
    hi: usize,
    strict: bool,
    lemma: &'static str,
    args: (usize, usize),
    fact: usize,
}

fn rows_of(reading: &Reading, lo: usize, hi: usize, fact: usize) -> Vec<Row> {
    let row = |lo, hi, strict, lemma| Row { lo, hi, strict, lemma, args: (lo, hi), fact };
    match reading {
        Reading::Stated(s) => match s.rel {
            Rel::Le => vec![row(lo, hi, false, "lin_le_part")],
            Rel::Lt => vec![row(lo, hi, true, "lin_lt_part")],
            Rel::Same => vec![
                row(lo, hi, false, "lin_same_part"),
                Row { lo: hi, hi: lo, strict: false, lemma: "lin_same_part_rev", args: (lo, hi), fact },
            ],
        },
        // `¬(x < y)` is `y <= x`: the caller passes `lo = y`, `hi = x`.
        Reading::NotLt(_) => vec![row(lo, hi, false, "lin_not_lt_part")],
    }
}

/// A row of the elimination: `Σ coeffs·m + constant ≥ 0` (`> 0` when
/// strict), and the combination of the problem's rows it is.
#[derive(Clone, Debug)]
struct FmRow {
    coeffs: BTreeMap<Vec<u32>, Z>,
    constant: Z,
    strict: bool,
    origin: Vec<Z>,
}

fn overflow() -> String {
    "`linarith`: a coefficient overflowed 128 bits".into()
}

fn gcd(mut a: Z, mut b: Z) -> Z {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl FmRow {
    fn contradiction(&self) -> bool {
        self.coeffs.is_empty() && (self.constant < 0 || (self.constant == 0 && self.strict))
    }

    fn trivial(&self) -> bool {
        self.coeffs.is_empty() && !self.contradiction()
    }

    /// `self·a + other·b`, for positive `a` and `b`, divided by the
    /// greatest common divisor of everything it carries.
    fn combine(&self, a: Z, other: &FmRow, b: Z) -> Result<FmRow, String> {
        let mut coeffs = BTreeMap::new();
        for (m, c) in &self.coeffs {
            coeffs.insert(m.clone(), c.checked_mul(a).ok_or_else(overflow)?);
        }
        for (m, c) in &other.coeffs {
            let entry = coeffs.entry(m.clone()).or_insert(0);
            *entry = c.checked_mul(b).and_then(|d| entry.checked_add(d)).ok_or_else(overflow)?;
        }
        coeffs.retain(|_, c| *c != 0);
        let constant = self
            .constant
            .checked_mul(a)
            .zip(other.constant.checked_mul(b))
            .and_then(|(x, y)| x.checked_add(y))
            .ok_or_else(overflow)?;
        let origin = self
            .origin
            .iter()
            .zip(&other.origin)
            .map(|(x, y)| x.checked_mul(a).zip(y.checked_mul(b)).and_then(|(x, y)| x.checked_add(y)).ok_or_else(overflow))
            .collect::<Result<Vec<_>, String>>()?;
        let mut row = FmRow { coeffs, constant, strict: self.strict || other.strict, origin };
        row.reduce();
        Ok(row)
    }

    fn reduce(&mut self) {
        let g = self
            .coeffs
            .values()
            .chain(std::iter::once(&self.constant))
            .chain(&self.origin)
            .fold(0, |g, c| gcd(g, *c));
        if g > 1 {
            self.coeffs.values_mut().for_each(|c| *c /= g);
            self.constant /= g;
            self.origin.iter_mut().for_each(|c| *c /= g);
        }
    }
}

/// Keeps, for each linear part, the strongest row: the least constant, a
/// strict one at a tie. Tautologies go.
fn prune(rows: Vec<FmRow>) -> Vec<FmRow> {
    let mut best: BTreeMap<Vec<(Vec<u32>, Z)>, FmRow> = BTreeMap::new();
    for row in rows {
        if row.trivial() {
            continue;
        }
        let key: Vec<(Vec<u32>, Z)> = row.coeffs.iter().map(|(m, c)| (m.clone(), *c)).collect();
        match best.get(&key) {
            Some(old) if (old.constant, !old.strict) <= (row.constant, !row.strict) => {}
            _ => {
                best.insert(key, row);
            }
        }
    }
    best.into_values().collect()
}

/// Fourier–Motzkin elimination: the combination of the rows that is a
/// contradiction, if there is one.
fn eliminate(rows: Vec<FmRow>) -> Result<Option<Vec<Z>>, String> {
    let mut rows = prune(rows);
    loop {
        if let Some(row) = rows.iter().find(|r| r.contradiction()) {
            return Ok(Some(row.origin.clone()));
        }
        let mut signs: BTreeMap<&Vec<u32>, (usize, usize)> = BTreeMap::new();
        for row in &rows {
            for (m, c) in &row.coeffs {
                let entry = signs.entry(m).or_default();
                if *c > 0 { entry.0 += 1 } else { entry.1 += 1 }
            }
        }
        // The variable whose elimination adds the fewest rows.
        let Some(var) = signs
            .iter()
            .min_by_key(|(_, (p, n))| (p * n) as i64 - (*p + *n) as i64)
            .map(|(m, _)| (*m).clone())
        else {
            return Ok(None);
        };
        let (with, mut next): (Vec<FmRow>, Vec<FmRow>) = rows.into_iter().partition(|r| r.coeffs.contains_key(&var));
        let (pos, neg): (Vec<&FmRow>, Vec<&FmRow>) = with.iter().partition(|r| r.coeffs[&var] > 0);
        for p in &pos {
            for n in &neg {
                let (a, b) = (p.coeffs[&var], -n.coeffs[&var]);
                let g = gcd(a, b);
                next.push(p.combine(b / g, n, a / g)?);
            }
        }
        rows = prune(next);
        if rows.len() > MAX_ROWS {
            return Err(format!("`linarith` gave up: eliminating the atoms produced more than {MAX_ROWS} inequalities"));
        }
    }
}

/// The goal, as the certificate proves it.
enum Goal {
    /// `a <= b` (`strict`: `a < b`).
    Order { a: usize, b: usize, strict: bool },
    /// `a ≈ b`: both orders.
    Same { a: usize, b: usize },
    /// `¬(a < b)`: `b <= a`.
    NotLt { a: usize, b: usize },
    /// Anything else, `False` among it: the facts must be contradictory.
    Absurd,
}

/// A fact the search may use: its proof's alias, its reading, and how it is
/// shown in a message.
struct Fact {
    alias: String,
    term: Term,
    ty: Type,
    level: Level,
    shown: String,
    written: Option<usize>,
    /// `nlinarith`'s assumed negation of the goal, bound by the certificate's
    /// own `λ __nlin_g`, not an alias (its term and type are placeholders).
    bound: bool,
}

/// A positive factor a row may be multiplied by: the denominator `d` of a
/// reciprocal atom `r`, which some fact shows positive. A row mentioning
/// `r` times `d` is the row with `r·d` read as `1` — the fact `ring` reads
/// with the reciprocal — so the scaled row says what the fraction does.
struct Factor {
    recip: usize,
    /// `d`'s linear form.
    form: Linear,
    /// How the certificate writes `d`, and a proof of `0 < d` there.
    source: String,
    proof: String,
    /// The fact the proof cites.
    fact: usize,
}

/// The most denominators one row is multiplied by.
const MAX_SCALINGS: usize = 2;

/// A row as the elimination uses it: a fact's row, or the goal's negation
/// (`row: None`), multiplied by the factors `by`, with its linear form
/// after the multiplication.
struct Use {
    row: Option<usize>,
    by: Vec<usize>,
    form: Linear,
    strict: bool,
    /// One of `nlinarith`'s parts instead (`Problem::extras`).
    extra: Option<usize>,
}

/// A part `nlinarith` adds (docs/nonlinear-arithmetic-design.md §4): the
/// product of two rows' differences, or a square, as the certificate writes
/// it, the proof that it is on the right side of zero, and its form.
struct Extra {
    source: String,
    proof: String,
    strict: bool,
    form: Linear,
    /// The facts the proof cites.
    facts: Vec<usize>,
}

/// The most rows `nlinarith` multiplies pairwise: the products grow with
/// the square of it, and the elimination's input with them.
const MAX_PRODUCT_ROWS: usize = 12;

/// `form·d` with `r·d` read as `1`: a monomial with `r` loses one `r`, any
/// other is multiplied by `d`.
fn scale(form: &Linear, factor: &Factor) -> Result<Linear, String> {
    let mut out: BTreeMap<Vec<u32>, Z> = BTreeMap::new();
    let mut add = |m: Vec<u32>, c: Z| -> Result<(), String> {
        let entry = out.entry(m).or_insert(0);
        *entry = entry.checked_add(c).ok_or_else(overflow)?;
        Ok(())
    };
    let r = factor.recip;
    let terms = form.0.iter().map(|(m, c)| (m.clone(), *c)).chain(std::iter::once((Vec::new(), form.1)));
    let den: Vec<(Vec<u32>, Z)> =
        factor.form.0.iter().map(|(m, c)| (m.clone(), *c)).chain(std::iter::once((Vec::new(), factor.form.1))).collect();
    for (m, c) in terms {
        if c == 0 {
            continue;
        }
        if m.get(r).is_some_and(|e| *e > 0) {
            let mut m = m;
            m[r] -= 1;
            while m.last() == Some(&0) {
                m.pop();
            }
            add(m, c)?;
        } else {
            for (dm, dc) in &den {
                if *dc != 0 {
                    add(FieldReading::monomial_product(&m, dm)?, c.checked_mul(*dc).ok_or_else(overflow)?)?;
                }
            }
        }
    }
    let constant = out.remove(&Vec::new()).unwrap_or(0);
    out.retain(|_, c| *c != 0);
    Ok((out, constant))
}

fn mentions(form: &Linear, atom: usize) -> bool {
    form.0.keys().any(|m| m.get(atom).is_some_and(|e| *e > 0))
}

struct Problem<'a> {
    reading: FieldReading<'a>,
    carrier: String,
    spell: Spell,
    carrier_ty: Rc<Type>,
    carrier_level: Level,
    terms: Vec<Rc<Term>>,
    forms: Vec<Linear>,
    rows: Vec<Row>,
    facts: Vec<Fact>,
    factors: Vec<Factor>,
    /// The reciprocals whose positivity by construction is a fact already.
    constructed: Vec<usize>,
    /// `nlinarith`'s products and squares, rebuilt for each search.
    extras: Vec<Extra>,
    /// Whether the context's facts are multiplied too (`nlinarith`'s second
    /// pass), not only the written ones and the goal's negation.
    multiply_context: bool,
    /// The carrier's lemma reading `a < b` off a refutation of `b <= a`,
    /// where its order is decided (`Rat`): `nlinarith` may then multiply the
    /// negation of a strict goal too.
    decided_lt: Option<String>,
}

fn term_alias(i: usize) -> String {
    format!("__lin_t{i}")
}

impl Problem<'_> {
    /// The index of `tm` in the term table, read as a linear form.
    fn term(&mut self, tm: &Rc<Term>) -> Result<usize, String> {
        if let Some(i) = self.terms.iter().position(|t| t == tm) {
            return Ok(i);
        }
        let form = self.reading.linear(tm)?;
        self.terms.push(Rc::clone(tm));
        self.forms.push(form);
        Ok(self.terms.len() - 1)
    }

    /// Adds a fact at this carrier; `false` (and nothing added) for one at
    /// another carrier or that does not read.
    fn add_fact(&mut self, elab: &Elaborator, cx: &Cx, fact: Fact, span: Span) -> bool {
        let Some(reading) = Reading::of(elab, cx, &fact.ty, span) else {
            return false;
        };
        let s = reading.stated();
        if elab.spell_type_clean(cx, &s.carrier).as_deref() != Some(self.carrier.as_str()) {
            return false;
        }
        let (terms, forms) = (self.terms.len(), self.forms.len());
        let (left, right) = (Rc::clone(&s.left), Rc::clone(&s.right));
        let sides = self.term(&left).and_then(|l| Ok((l, self.term(&right)?)));
        let Ok((l, r)) = sides else {
            self.terms.truncate(terms);
            self.forms.truncate(forms);
            return false;
        };
        let (lo, hi) = match reading {
            Reading::Stated(_) => (l, r),
            Reading::NotLt(_) => (r, l),
        };
        let index = self.facts.len();
        self.rows.extend(rows_of(&reading, lo, hi, index));
        self.facts.push(fact);
        true
    }

    /// The facts the reading's reciprocals bring: `0 < r` for one positive
    /// by construction (`Rat::inv_succ_pos`), then each denominator a fact
    /// shows positive, as a factor rows may be multiplied by.
    fn add_denominators(&mut self, elab: &Elaborator, cx: &Cx, span: Span) {
        // A constructed fact's sides can meet another reciprocal.
        loop {
            let pending: Vec<(usize, Term, Type, Level, String)> = self
                .reading
                .reciprocals()
                .iter()
                .filter(|r| !self.constructed.contains(&r.atom))
                .filter_map(|r| r.positive.clone().map(|(term, ty, level, shown)| (r.atom, term, ty, level, shown)))
                .collect();
            if pending.is_empty() {
                break;
            }
            for (atom, term, ty, level, shown) in pending {
                self.constructed.push(atom);
                let alias = format!("__lin_h{}", self.facts.len());
                self.add_fact(elab, cx, Fact { alias, term, ty, level, shown, written: None, bound: false }, span);
            }
        }
        self.factors.clear();
        let recips: Vec<(usize, Rc<Term>)> = self.reading.reciprocals().iter().map(|r| (r.atom, Rc::clone(&r.den))).collect();
        for (recip, den) in recips {
            let Ok(d) = self.term(&den) else { continue };
            let form = self.forms[d].clone();
            if mentions(&form, recip) {
                continue;
            }
            let alone = (BTreeMap::from([(FieldReading::atom_monomial(recip), 1)]), 0);
            let c = &self.carrier;
            // A strict fact whose difference is `d` itself, else one whose
            // difference is `r`: then `d` is positive as `r`'s denominator.
            let mut found = None;
            for row in self.rows.iter().filter(|row| row.strict) {
                let Ok(diff) = self.difference(row.lo, row.hi) else { continue };
                let source = self.spell.diff(&term_alias(row.hi), &term_alias(row.lo));
                let base = self.part(row);
                if diff == form {
                    found = Some(Factor { recip, form: form.clone(), source, proof: base, fact: row.fact });
                    break;
                }
                if diff == alone && found.is_none() {
                    let td = term_alias(d);
                    let one = self.spell.num(1);
                    let proof = format!(
                        "{{ let __lin_d: ({source} * {td} ≈ {one}) = ring; linarith::lin_den_pos<{c}>({source}, {td}, {base}, __lin_d) }}"
                    );
                    found = Some(Factor { recip, form: form.clone(), source: td, proof, fact: row.fact });
                }
            }
            self.factors.extend(found);
        }
    }

    /// `hi − lo` as a linear form.
    fn difference(&self, lo: usize, hi: usize) -> Result<Linear, String> {
        let (mut terms, mut constant) = self.forms[hi].clone();
        for (m, c) in &self.forms[lo].0 {
            let entry = terms.entry(m.clone()).or_insert(0);
            *entry = entry.checked_sub(*c).ok_or_else(overflow)?;
        }
        terms.retain(|_, c| *c != 0);
        constant = constant.checked_sub(self.forms[lo].1).ok_or_else(overflow)?;
        Ok((terms, constant))
    }

    /// The proof that a row's difference is on the right side of zero.
    fn part(&self, row: &Row) -> String {
        format!(
            "linarith::{}<{}>({}, {}, {})",
            row.lemma,
            self.carrier,
            term_alias(row.args.0),
            term_alias(row.args.1),
            self.facts[row.fact].alias
        )
    }

    /// A form and the same form multiplied by each set of at most
    /// `MAX_SCALINGS` factors whose reciprocals it mentions, one at a time.
    fn uses(&self, row: Option<usize>, form: Linear, strict: bool) -> Result<Vec<Use>, String> {
        let mut out = vec![Use { row, by: Vec::new(), form, strict, extra: None }];
        let mut next = 0;
        while next < out.len() {
            if out[next].by.len() < MAX_SCALINGS {
                for (j, factor) in self.factors.iter().enumerate() {
                    if out[next].by.contains(&j) || !mentions(&out[next].form, factor.recip) {
                        continue;
                    }
                    let mut by = out[next].by.clone();
                    by.push(j);
                    let mut key = by.clone();
                    key.sort();
                    if out.iter().any(|u| {
                        let mut k = u.by.clone();
                        k.sort();
                        k == key
                    }) {
                        continue;
                    }
                    let form = scale(&out[next].form, factor)?;
                    out.push(Use { row, by, form, strict, extra: None });
                }
            }
            next += 1;
        }
        Ok(out)
    }

    /// Every fact's row with its scalings, and `nlinarith`'s parts.
    fn fact_uses(&self) -> Result<Vec<Use>, String> {
        let mut out = Vec::new();
        for (i, row) in self.rows.iter().enumerate() {
            out.extend(self.uses(Some(i), self.difference(row.lo, row.hi)?, row.strict)?);
        }
        for (e, extra) in self.extras.iter().enumerate() {
            out.push(Use { row: None, by: Vec::new(), form: extra.form.clone(), strict: extra.strict, extra: Some(e) });
        }
        Ok(out)
    }

    /// The product of the factors `by` and its positivity proof.
    fn product(&self, by: &[usize]) -> (String, String) {
        let c = &self.carrier;
        let (last, rest) = by.split_last().expect("a scaled row has a factor");
        let last = &self.factors[*last];
        rest.iter().rev().fold((last.source.clone(), last.proof.clone()), |(e, p), j| {
            let f = &self.factors[*j];
            (format!("({} * {e})", f.source), format!("linarith::lin_scale_lt<{c}>({}, {e}, {}, {p})", f.source, f.proof))
        })
    }

    /// A certificate for `a <= b` (or `a < b`), with the rows the problem
    /// has: the expression proving it, and the facts it cites.
    fn order(&self, a: usize, b: usize, strict: bool, names: &mut usize) -> Result<Option<(String, Vec<usize>)>, String> {
        // The goal's negation: `b < a` against `a <= b`, `b <= a` against
        // `a < b`, as `a − b` on the right side of zero.
        let mut uses = self.fact_uses()?;
        uses.extend(self.uses(None, self.difference(b, a)?, !strict)?);
        let Some(lambda) = eliminate(Self::fm_rows(&uses))? else {
            return Ok(None);
        };
        self.write(a, b, strict, &uses, &lambda, names).map(Some)
    }

    fn fm_rows(uses: &[Use]) -> Vec<FmRow> {
        uses.iter()
            .enumerate()
            .map(|(i, u)| {
                let mut origin = vec![0; uses.len()];
                origin[i] = 1;
                FmRow { coeffs: u.form.0.clone(), constant: u.form.1, strict: u.strict, origin }
            })
            .collect()
    }

    fn write(
        &self,
        a: usize,
        b: usize,
        strict: bool,
        uses: &[Use],
        lambda: &[Z],
        names: &mut usize,
    ) -> Result<(String, Vec<usize>), String> {
        // Check the combination before writing it, so a searcher bug is an
        // internal error rather than a `ring` failure.
        let mut sum: Linear = (BTreeMap::new(), 0);
        for (u, k) in uses.iter().zip(lambda) {
            for (m, c) in &u.form.0 {
                let entry = sum.0.entry(m.clone()).or_insert(0);
                *entry = c.checked_mul(*k).and_then(|d| entry.checked_add(d)).ok_or_else(overflow)?;
            }
            sum.1 = u.form.1.checked_mul(*k).and_then(|d| sum.1.checked_add(d)).ok_or_else(overflow)?;
        }
        sum.0.retain(|_, c| *c != 0);
        let strict_rows = uses.iter().zip(lambda).any(|(u, k)| *k > 0 && u.strict);
        if !sum.0.is_empty() || sum.1 > 0 || (sum.1 == 0 && !strict_rows) || lambda.iter().any(|l| *l < 0) {
            return Err("internal: `linarith`'s elimination returned a combination that is not a contradiction".into());
        }
        let c = &self.carrier;
        let num_pos = |k: Z| format!("linarith::lin_num_pos<{c}>({})", k - 1);
        let num = |k: Z| self.spell.num(k);
        let mut cited = Vec::new();
        let mut cite = |f: usize| {
            if !cited.contains(&f) {
                cited.push(f);
            }
        };
        // The parts `λᵢ·Pᵢ·(hiᵢ − loᵢ)`, then the constant, each with its
        // proof and whether it is strict; and the goal's multiplier
        // `Σ λⱼ·Pⱼ` over the uses of its negation, with its positivity.
        let mut parts: Vec<(String, String, bool)> = Vec::new();
        let mut multiplier: Vec<(String, String)> = Vec::new();
        for (u, &k) in uses.iter().zip(lambda) {
            if k == 0 {
                continue;
            }
            for j in &u.by {
                cite(self.factors[*j].fact);
            }
            if let Some(e) = u.extra {
                let extra = &self.extras[e];
                extra.facts.iter().for_each(|f| cite(*f));
                let scale_lemma = if extra.strict { "lin_scale_lt" } else { "lin_scale_le" };
                let mut part = (extra.source.clone(), extra.proof.clone());
                if k != 1 {
                    let n = num(k);
                    part = (format!("{n} * {}", part.0), format!("linarith::{scale_lemma}<{c}>({n}, {}, {}, {})", part.0, num_pos(k), part.1));
                }
                parts.push((part.0, part.1, extra.strict));
                continue;
            }
            let Some(i) = u.row else {
                multiplier.push(match (u.by.is_empty(), k) {
                    (true, _) => (num(k), num_pos(k)),
                    (false, 1) => self.product(&u.by),
                    (false, _) => {
                        let (e, p) = self.product(&u.by);
                        let n = num(k);
                        (format!("({n} * {e})"), format!("linarith::lin_scale_lt<{c}>({n}, {e}, {}, {p})", num_pos(k)))
                    }
                });
                continue;
            };
            let row = &self.rows[i];
            cite(row.fact);
            // `hi + -lo`, not `hi - lo`: the lemmas state the difference
            // with the group's negation, and the argument must meet their
            // statement before the instance is chosen, so a `sub` that only
            // unfolds to it would not.
            let scale_lemma = if row.strict { "lin_scale_lt" } else { "lin_scale_le" };
            let mut part = (self.spell.diff(&term_alias(row.hi), &term_alias(row.lo)), self.part(row));
            if !u.by.is_empty() {
                let (e, p) = self.product(&u.by);
                part = (format!("({e} * {})", part.0), format!("linarith::{scale_lemma}<{c}>({e}, {}, {p}, {})", part.0, part.1));
            }
            if k != 1 {
                let n = num(k);
                part = (format!("{n} * {}", part.0), format!("linarith::{scale_lemma}<{c}>({n}, {}, {}, {})", part.0, num_pos(k), part.1));
            }
            parts.push((part.0, part.1, row.strict));
        }
        let constant = -sum.1;
        if constant > 0 {
            parts.push((num(constant), num_pos(constant), true));
        }
        let (s, hs, positive) = match parts.pop() {
            None => (num(0), format!("linarith::lin_zero_le<{c}>()"), false),
            Some(last) => parts.into_iter().rev().fold(last, |(e, p, st), (ei, pi, si)| {
                let lemma = match (si, st) {
                    (false, false) => "lin_add_le_le",
                    (true, false) => "lin_add_lt_le",
                    (false, true) => "lin_add_le_lt",
                    (true, true) => "lin_add_lt_lt",
                };
                (format!("({ei} + {e})"), format!("linarith::{lemma}<{c}>({ei}, {e}, {pi}, {p})"), si || st)
            }),
        };
        let name = format!("__lin_e{names}");
        *names += 1;
        let (ta, tb) = (term_alias(a), term_alias(b));
        let source = match multiplier.pop() {
            None => format!(
                "logic::false_elim({{ let {name}: ({s} ≈ {}) = ring; linarith::lin_finish_false<{c}>({s}, {hs}, {name}) }})",
                num(0)
            ),
            Some(last) => {
                let (k, hk) = multiplier.into_iter().rev().fold(last, |(e, p), (ei, pi)| {
                    (format!("({ei} + {e})"), format!("linarith::lin_add_lt_lt<{c}>({ei}, {e}, {pi}, {p})"))
                });
                let (finish, hs) = if strict {
                    ("lin_finish_lt", hs)
                } else if positive {
                    ("lin_finish_le", format!("linarith::lin_weaken<{c}>({s}, {hs})"))
                } else {
                    ("lin_finish_le", hs)
                };
                let diff = self.spell.diff(&tb, &ta);
                format!(
                    "{{ let {name}: ({k} * {diff} ≈ {s}) = ring; linarith::{finish}<{c}>({ta}, {tb}, {k}, {s}, {hk}, {hs}, {name}) }}"
                )
            }
        };
        Ok((source, cited))
    }

    /// An atom as the certificate writes it: the alias of its term.
    fn atom_source(&mut self, atom: usize) -> Result<String, String> {
        let tm = self.reading.atom_terms().get(atom).cloned().ok_or("internal: an atom out of the reading's table")?;
        let i = self.term(&tm)?;
        if self.forms[i] != (BTreeMap::from([(FieldReading::atom_monomial(atom), 1)]), 0) {
            return Err("internal: an atom's term did not read as that atom".into());
        }
        Ok(term_alias(i))
    }

    /// A form as source at the carrier, over its atoms' aliases.
    fn form_source(&mut self, form: &Linear) -> Result<String, String> {
        let mut parts = Vec::new();
        for (m, c) in form.0.clone() {
            let mut factors = Vec::new();
            for (atom, e) in m.iter().enumerate() {
                for _ in 0..*e {
                    factors.push(self.atom_source(atom)?);
                }
            }
            let monomial = factors.join(" * ");
            let body = if c.abs() == 1 { monomial } else { format!("{} * {monomial}", self.spell.num(c.abs())) };
            parts.push(if c < 0 { self.spell.neg(&format!("({body})")) } else { format!("({body})") });
        }
        if form.1 != 0 || parts.is_empty() {
            parts.push(self.spell.num(form.1));
        }
        Ok(format!("({})", parts.join(" + ")))
    }

    /// `nlinarith`'s parts (docs/nonlinear-arithmetic-design.md §4.2): the
    /// product of every pair of the rows it multiplies — the goal's assumed
    /// negation, the written facts, and in the second pass the context's —
    /// each row with itself included; and a square for each base the terms
    /// write squared (`t * t`) and for each monomial whose exponents are all
    /// even.
    fn add_products(&mut self) -> Result<(), String> {
        self.extras.clear();
        let c = self.carrier.clone();
        let mut chosen: Vec<usize> = Vec::new();
        for class in 0..3 {
            for (i, row) in self.rows.iter().enumerate() {
                let fact = &self.facts[row.fact];
                let of = if fact.bound {
                    0
                } else if fact.written.is_some() {
                    1
                } else {
                    2
                };
                if of == class && (class < 2 || self.multiply_context) {
                    chosen.push(i);
                }
            }
        }
        chosen.truncate(MAX_PRODUCT_ROWS);
        // Each chosen row's difference as written, its proof, strictness,
        // form and fact.
        let mut rows = Vec::new();
        for &i in &chosen {
            let row = &self.rows[i];
            let source = self.spell.diff(&term_alias(row.hi), &term_alias(row.lo));
            rows.push((source, self.part(row), row.strict, self.difference(row.lo, row.hi)?, row.fact));
        }
        let weak = |r: &(String, String, bool, Linear, usize)| {
            if r.2 { format!("linarith::lin_weaken<{c}>({}, {})", r.0, r.1) } else { r.1.clone() }
        };
        for (x, p) in rows.iter().enumerate() {
            for q in &rows[x..] {
                let form = FieldReading::product(&p.3, &q.3)?;
                let (proof, strict) = if p.2 && q.2 {
                    (format!("linarith::nlin_mul_lt<{c}>({}, {}, {}, {})", p.0, q.0, p.1, q.1), true)
                } else {
                    (format!("linarith::nlin_mul_le<{c}>({}, {}, {}, {})", p.0, q.0, weak(p), weak(q)), false)
                };
                let facts = if p.4 == q.4 { vec![p.4] } else { vec![p.4, q.4] };
                self.extras.push(Extra { source: format!("({} * {})", p.0, q.0), proof, strict, form, facts });
            }
        }
        let mut bases: Vec<Linear> = self.reading.squares().to_vec();
        let mut monomials: Vec<Vec<u32>> = self.forms.iter().flat_map(|f| f.0.keys().cloned()).collect();
        monomials.sort();
        monomials.dedup();
        for m in monomials {
            if m.iter().any(|e| *e > 0) && m.iter().all(|e| e % 2 == 0) {
                let root: Vec<u32> = m.iter().map(|e| e / 2).collect();
                let base = (BTreeMap::from([(root, 1)]), 0);
                if !bases.contains(&base) {
                    bases.push(base);
                }
            }
        }
        for base in bases {
            let source = self.form_source(&base)?;
            let form = FieldReading::product(&base, &base)?;
            self.extras.push(Extra {
                source: format!("({source} * {source})"),
                proof: format!("linarith::nlin_sq<{c}>({source})"),
                strict: false,
                form,
                facts: Vec::new(),
            });
        }
        Ok(())
    }

    /// `nlinarith`'s refutation: with `hi − lo` assumed on the right side of
    /// zero (the goal's negation, which the certificate binds as
    /// `__nlin_g`), the facts and their products are contradictory. The
    /// expression proves `False` under that binder.
    fn refute(&mut self, lo: usize, hi: usize, strict: bool, names: &mut usize) -> Result<Option<(String, Vec<usize>)>, String> {
        let fact = self.facts.len();
        self.facts.push(Fact {
            alias: "__nlin_g".into(),
            term: Term::Zero,
            ty: (*self.carrier_ty).clone(),
            level: self.carrier_level.clone(),
            shown: "the goal's negation".into(),
            written: None,
            bound: true,
        });
        let lemma = if strict { "lin_lt_part" } else { "lin_le_part" };
        self.rows.push(Row { lo, hi, strict, lemma, args: (lo, hi), fact });
        let found = self.add_products().and_then(|()| {
            let uses = self.fact_uses()?;
            match eliminate(Self::fm_rows(&uses))? {
                Some(lambda) => self.write(lo, hi, false, &uses, &lambda, names).map(Some),
                None => Ok(None),
            }
        });
        self.rows.pop();
        self.facts.pop();
        self.extras.clear();
        Ok(found?.map(|(proof, mut cited)| {
            cited.retain(|f| *f != fact);
            (proof, cited)
        }))
    }

    /// `nlinarith`'s certificate for the goal (design §2): a refutation
    /// wherever one proves the goal, so its negation is multiplied like a
    /// fact; a strict goal at a carrier whose order is not decided (`CReal`)
    /// keeps the direct form, its negation used linearly.
    fn prove_nonlinear(&mut self, goal: &Goal) -> Result<Option<(String, Vec<usize>)>, String> {
        let mut names = 0;
        let c = self.carrier.clone();
        let le_of = |a: usize, b: usize, body: String| {
            format!("linarith::nlin_le_of_refute<{c}>({}, {}, λ __nlin_g => {body})", term_alias(a), term_alias(b))
        };
        Ok(match *goal {
            Goal::Order { a, b, strict: false } => self.refute(b, a, true, &mut names)?.map(|(p, cited)| (le_of(a, b, p), cited)),
            Goal::Order { a, b, strict: true } => {
                self.add_products()?;
                let direct = self.order(a, b, true, &mut names)?;
                self.extras.clear();
                match (direct, self.decided_lt.clone()) {
                    (Some(found), _) => Some(found),
                    (None, Some(lemma)) => self.refute(b, a, false, &mut names)?.map(|(p, cited)| {
                        (format!("{lemma}(x := {}, y := {}, h := λ __nlin_g => {p})", term_alias(a), term_alias(b)), cited)
                    }),
                    (None, None) => None,
                }
            }
            Goal::Same { a, b } => {
                let Some((up, mut cited)) = self.refute(b, a, true, &mut names)? else {
                    return Ok(None);
                };
                let Some((down, more)) = self.refute(a, b, true, &mut names)? else {
                    return Ok(None);
                };
                cited.extend(more.into_iter().filter(|f| !cited.contains(f)).collect::<Vec<_>>());
                let (up, down) = (le_of(a, b, up), le_of(b, a, down));
                Some((format!("linarith::lin_same_of_le<{c}>({}, {}, {up}, {down})", term_alias(a), term_alias(b)), cited))
            }
            Goal::NotLt { a, b } => self.refute(a, b, true, &mut names)?.map(|(p, cited)| (format!("λ __nlin_g => {p}"), cited)),
            Goal::Absurd => {
                if self.terms.is_empty() {
                    return Ok(None);
                }
                self.add_products()?;
                let uses = self.fact_uses()?;
                let found = match eliminate(Self::fm_rows(&uses))? {
                    Some(lambda) => Some(self.write(0, 0, false, &uses, &lambda, &mut names)?),
                    None => None,
                };
                self.extras.clear();
                found
            }
        })
    }

    /// A certificate for the goal from the facts so far.
    fn prove(&self, goal: &Goal) -> Result<Option<(String, Vec<usize>)>, String> {
        let mut names = 0;
        let c = &self.carrier;
        Ok(match *goal {
            Goal::Order { a, b, strict } => self.order(a, b, strict, &mut names)?,
            Goal::NotLt { a, b } => self.order(b, a, false, &mut names)?.map(|(p, cited)| {
                (format!("linarith::lin_not_lt_of_le<{c}>({}, {}, {p})", term_alias(a), term_alias(b)), cited)
            }),
            Goal::Same { a, b } => {
                let Some((up, mut cited)) = self.order(a, b, false, &mut names)? else {
                    return Ok(None);
                };
                let Some((down, more)) = self.order(b, a, false, &mut names)? else {
                    return Ok(None);
                };
                cited.extend(more.into_iter().filter(|f| !cited.contains(f)).collect::<Vec<_>>());
                Some((format!("linarith::lin_same_of_le<{c}>({}, {}, {up}, {down})", term_alias(a), term_alias(b)), cited))
            }
            // With no goal row the elimination is over the facts alone; the
            // goal's sides are any two terms, never used.
            Goal::Absurd => {
                if self.terms.is_empty() {
                    return Ok(None);
                }
                let uses = self.fact_uses()?;
                match eliminate(Self::fm_rows(&uses))? {
                    Some(lambda) => Some(self.write(0, 0, false, &uses, &lambda, &mut names)?),
                    None => None,
                }
            }
        })
    }
}

// ---------------------------------------------------------------------------
// `Int` and `Nat`: `ring`'s monomials as `omega`'s atoms (design §8).

/// A product's spelling over the atoms' aliases, factors in atom order, so
/// one monomial is one term wherever it is written.
fn monomial_source(m: &[u32], alias: &dyn Fn(usize) -> String) -> String {
    let factors: Vec<String> = m.iter().enumerate().flat_map(|(i, e)| (0..*e).map(move |_| alias(i))).collect();
    match factors.len() {
        1 => factors[0].clone(),
        _ => format!("({})", factors.join(" * ")),
    }
}

/// A linear form over monomials as source at `Int` (`nat` false) or `Nat`:
/// the positive terms less the negative ones, so no numeral is negative.
fn integral_form_source(form: &Linear, nat: bool, alias: &dyn Fn(usize) -> String) -> Result<String, String> {
    let numeral = |c: u128| if nat { c.to_string() } else { format!("int::OfNat({c})") };
    let term = |m: &[u32], c: u128| match c {
        1 => monomial_source(m, alias),
        _ => format!("{} * {}", numeral(c), monomial_source(m, alias)),
    };
    let (mut pos, mut neg) = (Vec::new(), Vec::new());
    for (m, c) in &form.0 {
        if *c > 0 { &mut pos } else { &mut neg }.push(term(m, c.unsigned_abs()));
    }
    if form.1 > 0 {
        pos.push(numeral(form.1.unsigned_abs()));
    } else if form.1 < 0 {
        neg.push(numeral(form.1.unsigned_abs()));
    }
    if nat && !neg.is_empty() {
        return Err("internal: a `Nat` side read with a negative coefficient".into());
    }
    let sum = |parts: &[String]| if parts.is_empty() { numeral(0) } else { parts.join(" + ") };
    Ok(if neg.is_empty() { sum(&pos) } else { format!("({}) - ({})", sum(&pos), sum(&neg)) })
}

/// What `linarith` reads at `Int` and `Nat`: each side of the goal and of
/// the facts, at its own carrier, over one atom table per carrier.
struct Integral<'a> {
    ints: FieldReading<'a>,
    nats: FieldReading<'a>,
    /// Each side once: its term, carrier, form, and whether it multiplies
    /// (then the certificate states it equal to its form).
    sides: Vec<(Rc<Term>, bool, Linear, bool)>,
    facts: Vec<Fact>,
    /// Written equations that define an atom, `t = e` with `t` not in `e`:
    /// the carrier, the atom, its definition's form, and the fact's alias.
    /// A side that mentions `t` is stated equal to its form with `e` for
    /// `t`, which `ring` proves from the equation (`(y * z).den.int() =
    /// q * r` makes `(a * e) * (y * z).den.int()` the monomial `a·e·q·r`).
    defs: Vec<(bool, usize, Linear, String)>,
    /// `nlinarith` (docs/nonlinear-arithmetic-design.md §4.4): the orders it
    /// multiplies pairwise, and how the certificate reads the goal back from
    /// a refutation, the source around `λ __nlin_g => …`.
    nonlinear: bool,
    orders: Vec<IntOrder>,
    refute: Option<(IntOrder, String, String)>,
}

/// An order at `Int` or `Nat` that `nlinarith` multiplies: `lo <= hi` or
/// `lo < hi` over the sides' indices, and its proof as source (a negated
/// fact goes through its carrier's `le_of_not_lt`/`lt_of_not_le`).
#[derive(Clone)]
struct IntOrder {
    nat: bool,
    lo: usize,
    hi: usize,
    strict: bool,
    proof: String,
}

fn integral_alias(nat: bool, i: usize) -> String {
    format!("__lin_{}{i}", if nat { 'n' } else { 'i' })
}

/// `a − b`.
fn form_sub(a: &Linear, b: &Linear) -> Result<Linear, String> {
    let (mut terms, constant) = a.clone();
    for (m, c) in &b.0 {
        let entry = terms.entry(m.clone()).or_insert(0);
        *entry = entry.checked_sub(*c).ok_or_else(overflow)?;
    }
    terms.retain(|_, c| *c != 0);
    Ok((terms, constant.checked_sub(b.1).ok_or_else(overflow)?))
}

/// `a + b`.
fn form_add(a: &Linear, b: &Linear) -> Result<Linear, String> {
    let negated: Linear = (b.0.iter().map(|(m, c)| (m.clone(), -c)).collect(), -b.1);
    form_sub(a, &negated)
}

impl Integral<'_> {
    fn side(&mut self, tm: &Rc<Term>, nat: bool) -> Result<(), String> {
        if self.sides.iter().any(|(t, n, _, _)| t == tm && *n == nat) {
            return Ok(());
        }
        let (form, product) = if nat { self.nats.read(tm)? } else { self.ints.read(tm)? };
        self.sides.push((Rc::clone(tm), nat, form, product));
        Ok(())
    }

    /// The facts' and the goal's sides; one that does not read is left to
    /// `omega` as written.
    fn sides_of(&mut self, elab: &Elaborator, cx: &Cx, ty: &Type) -> bool {
        let Some((nat, left, right)) = crate::omega_cert::integral_sides(elab, cx, ty) else {
            return false;
        };
        let _ = self.side(&left, nat);
        let _ = self.side(&right, nat);
        true
    }

    /// Records a written equation `t = e` (or `e = t`) whose one side is an
    /// atom alone and whose other does not mention it.
    fn definition(&mut self, elab: &Elaborator, cx: &Cx, ty: &Type, alias: &str) {
        let decoded = crate::inductive::decoded(ty);
        if !matches!(&*decoded, Type::Id { .. }) {
            return;
        }
        let Some((nat, left, right)) = crate::omega_cert::integral_sides(elab, cx, ty) else {
            return;
        };
        let form = |tm: &Rc<Term>| self.sides.iter().find(|(t, n, _, _)| t == tm && *n == nat).map(|side| side.2.clone());
        let (Some(l), Some(r)) = (form(&left), form(&right)) else {
            return;
        };
        let alone = |f: &Linear| match (f.0.iter().next(), f.0.len(), f.1) {
            (Some((m, 1)), 1, 0) if m.iter().sum::<u32>() == 1 => m.iter().position(|e| *e == 1),
            _ => None,
        };
        for (atom, by) in [(alone(&l), &r), (alone(&r), &l)] {
            if let Some(atom) = atom
                && !mentions(by, atom)
                && !self.defs.iter().any(|d| d.0 == nat && d.1 == atom)
            {
                self.defs.push((nat, atom, by.clone(), alias.to_string()));
                return;
            }
        }
    }

    /// A side's form with every definition applied, and the definitions'
    /// facts it took; an error past the substitutions a cycle would need.
    fn defined(&self, form: &Linear, nat: bool) -> Result<(Linear, Vec<String>), String> {
        let mut form = form.clone();
        let mut used = Vec::new();
        for _ in 0..=self.defs.len() {
            let Some(def) = self.defs.iter().find(|d| d.0 == nat && mentions(&form, d.1)) else {
                return Ok((form, used));
            };
            form = FieldReading::substitute(&form, def.1, &def.2)?;
            if !used.contains(&def.3) {
                used.push(def.3.clone());
            }
        }
        Err("the written equations define atoms in terms of each other".into())
    }

    /// The certificate: each side that multiplies stated equal to its form
    /// over monomials by `ring`, and `omega` over the facts and those
    /// equations, every monomial one atom to it.
    fn source(&self) -> Result<String, String> {
        let mut lets = String::new();
        let mut args: Vec<String> = self.facts.iter().map(|f| f.alias.clone()).collect();
        for (i, (_, nat, form, product)) in self.sides.iter().enumerate() {
            let nat = *nat;
            let (defined, used) = self.defined(form, nat)?;
            // A definition's own atom side is its fact already.
            let own = self.defs.iter().any(|d| d.0 == nat && *form == (BTreeMap::from([(FieldReading::atom_monomial(d.1), 1)]), 0));
            if !product && (used.is_empty() || own) {
                continue;
            }
            let source = integral_form_source(&defined, nat, &|j| integral_alias(nat, j))?;
            let name = format!("__lin_b{i}");
            let ring = if used.is_empty() { "ring".to_string() } else { format!("ring({})", used.join(", ")) };
            lets.push_str(&format!("let {name}: ({} = {source}) = {ring}; ", term_alias(i)));
            args.push(name);
        }
        if self.nonlinear {
            self.products(&mut lets, &mut args)?;
        }
        if let Some((_, open, close)) = &self.refute {
            args.push("__nlin_g".into());
            return Ok(format!("{open}{{ {lets}omega({}) }}{close}", args.join(", ")));
        }
        let omega = if args.is_empty() { "omega".to_string() } else { format!("omega({})", args.join(", ")) };
        Ok(if lets.is_empty() { omega } else { format!("{{ {lets}{omega} }}") })
    }

    fn side_index(&self, tm: &Rc<Term>, nat: bool) -> Option<usize> {
        self.sides.iter().position(|(t, n, _, _)| t == tm && *n == nat)
    }

    /// `ty` as an order `nlinarith` multiplies, proved by `proof`: `a <= b`,
    /// `a < b`, or the negation of one, which is the other the other way.
    fn order_of(&mut self, elab: &Elaborator, cx: &Cx, ty: &Type, proof: &str) -> Option<IntOrder> {
        let (direct, (nat, strict, l, r)) = match crate::omega_cert::integral_order(elab, ty) {
            Some(order) => (true, order),
            None => (false, crate::omega_cert::integral_order(elab, &negated_domain(elab, cx, ty)?)?),
        };
        self.side(&l, nat).ok()?;
        self.side(&r, nat).ok()?;
        let (li, ri) = (self.side_index(&l, nat)?, self.side_index(&r, nat)?);
        let module = if nat { "nat::Nat" } else { "int::Int" };
        let (tl, tr) = (term_alias(li), term_alias(ri));
        Some(match (direct, strict) {
            (true, _) => IntOrder { nat, lo: li, hi: ri, strict, proof: proof.into() },
            // `¬(l < r)` is `r <= l`; `¬(l <= r)` is `r < l`.
            (false, true) => IntOrder { nat, lo: ri, hi: li, strict: false, proof: format!("{module}::le_of_not_lt({tl}, {tr}, {proof})") },
            (false, false) => IntOrder { nat, lo: ri, hi: li, strict: true, proof: format!("{module}::lt_of_not_le({tr}, {tl}, {proof})") },
        })
    }

    /// The goal's negation as an order assumed under `__nlin_g`, and the
    /// source that reads the goal back from a proof of `False` under it.
    fn refutation(&mut self, elab: &Elaborator, cx: &Cx, goal: &Type) -> Option<(IntOrder, String, String)> {
        let g = |nat, lo, hi, strict| IntOrder { nat, lo, hi, strict, proof: "__nlin_g".into() };
        if let Some((nat, strict, a, b)) = crate::omega_cert::integral_order(elab, goal) {
            let (ai, bi) = (self.side_index(&a, nat)?, self.side_index(&b, nat)?);
            let module = if nat { "nat::Nat" } else { "int::Int" };
            let (ta, tb) = (term_alias(ai), term_alias(bi));
            return Some(if strict {
                // `a < b` from a refutation of `b <= a`.
                (g(nat, bi, ai, false), format!("{module}::lt_of_not_le({ta}, {tb}, λ __nlin_g => "), ")".into())
            } else {
                // `a <= b` from a refutation of `b < a`.
                (g(nat, bi, ai, true), format!("{module}::le_of_not_lt({tb}, {ta}, λ __nlin_g => "), ")".into())
            });
        }
        let (nat, strict, l, r) = crate::omega_cert::integral_order(elab, &negated_domain(elab, cx, goal)?)?;
        let (li, ri) = (self.side_index(&l, nat)?, self.side_index(&r, nat)?);
        Some((g(nat, li, ri, strict), "λ __nlin_g => ".into(), String::new()))
    }

    /// `nlinarith`'s lets: each pair of orders multiplied, stated over the
    /// sides and, by `ring`, over monomials; and at `Int` each square the
    /// terms write and each monomial with only even exponents, the same way.
    fn products(&self, lets: &mut String, args: &mut Vec<String>) -> Result<(), String> {
        let mut orders: Vec<&IntOrder> = self.refute.iter().map(|r| &r.0).chain(&self.orders).collect();
        orders.truncate(MAX_PRODUCT_ROWS);
        let t = term_alias;
        let tag = |o: &IntOrder| if o.strict { "lt" } else { "le" };
        let diff = |o: &IntOrder| -> Result<(Linear, Vec<String>), String> {
            let (hi, mut used) = self.defined(&self.sides[o.hi].2, o.nat)?;
            let (lo, more) = self.defined(&self.sides[o.lo].2, o.nat)?;
            used.extend(more.into_iter().filter(|d| !used.contains(d)).collect::<Vec<_>>());
            Ok((form_sub(&hi, &lo)?, used))
        };
        let ring = |used: &[String]| if used.is_empty() { "ring".to_string() } else { format!("ring({})", used.join(", ")) };
        let mut k = 0;
        for (x, p) in orders.iter().enumerate() {
            for q in &orders[x..] {
                if p.nat != q.nat {
                    continue;
                }
                let nat = p.nat;
                let alias = |j| integral_alias(nat, j);
                let args_of = format!("{}, {}, {}, {}, {}, {}", t(p.lo), t(p.hi), t(q.lo), t(q.hi), p.proof, q.proof);
                if nat {
                    // `a·d + b·c <= a·c + b·d` for `a <= b`, `c <= d`; a
                    // strict fact's low side is `a + 1`.
                    let mut used: Vec<String> = Vec::new();
                    let mut form = |i: usize, succ: bool| -> Result<Linear, String> {
                        let (f, more) = self.defined(&self.sides[i].2, true)?;
                        used.extend(more.into_iter().filter(|d| !used.contains(d)).collect::<Vec<_>>());
                        Ok((f.0, f.1 + Z::from(succ)))
                    };
                    let (fa, fb, fc, fd) = (form(p.lo, p.strict)?, form(p.hi, false)?, form(q.lo, q.strict)?, form(q.hi, false)?);
                    let low = |o: &IntOrder| if o.strict { format!("({} + 1)", t(o.lo)) } else { t(o.lo) };
                    let (a, b, c, d) = (low(p), t(p.hi), low(q), t(q.hi));
                    let left = format!("{a} * {d} + {b} * {c}");
                    let right = format!("{a} * {c} + {b} * {d}");
                    let left_form = form_add(&FieldReading::product(&fa, &fd)?, &FieldReading::product(&fb, &fc)?)?;
                    let right_form = form_add(&FieldReading::product(&fa, &fc)?, &FieldReading::product(&fb, &fd)?)?;
                    lets.push_str(&format!(
                        "let __nlin_p{k}: ({left} <= {right}) = linarith::nlin_nat_{}_{}({args_of}); \
                         let __nlin_l{k}: ({left} = {}) = {}; let __nlin_r{k}: ({right} = {}) = {}; ",
                        tag(p),
                        tag(q),
                        integral_form_source(&left_form, true, &alias)?,
                        ring(&used),
                        integral_form_source(&right_form, true, &alias)?,
                        ring(&used),
                    ));
                    args.extend([format!("__nlin_p{k}"), format!("__nlin_l{k}"), format!("__nlin_r{k}")]);
                } else {
                    let ((dp, mut used), (dq, more)) = (diff(p)?, diff(q)?);
                    used.extend(more.into_iter().filter(|d| !used.contains(d)).collect::<Vec<_>>());
                    let product = format!("({} - {}) * ({} - {})", t(p.hi), t(p.lo), t(q.hi), t(q.lo));
                    let rel = if p.strict && q.strict { "<" } else { "<=" };
                    let form = FieldReading::product(&dp, &dq)?;
                    lets.push_str(&format!(
                        "let __nlin_p{k}: (int::OfNat(0) {rel} {product}) = linarith::nlin_int_{}_{}({args_of}); \
                         let __nlin_q{k}: ({product} = {}) = {}; ",
                        tag(p),
                        tag(q),
                        integral_form_source(&form, false, &alias)?,
                        ring(&used),
                    ));
                    args.extend([format!("__nlin_p{k}"), format!("__nlin_q{k}")]);
                }
                k += 1;
            }
        }
        let mut bases: Vec<Linear> = self.ints.squares().to_vec();
        let mut monomials: Vec<Vec<u32>> =
            self.sides.iter().filter(|side| !side.1).flat_map(|side| side.2.0.keys().cloned()).collect();
        monomials.sort();
        monomials.dedup();
        for m in monomials {
            if m.iter().any(|e| *e > 0) && m.iter().all(|e| e % 2 == 0) {
                let base = (BTreeMap::from([(m.iter().map(|e| e / 2).collect::<Vec<u32>>(), 1)]), 0);
                if !bases.contains(&base) {
                    bases.push(base);
                }
            }
        }
        let alias = |j| integral_alias(false, j);
        for (j, base) in bases.iter().enumerate() {
            let e = integral_form_source(base, false, &alias)?;
            let form = FieldReading::product(base, base)?;
            lets.push_str(&format!(
                "let __nlin_s{j}: (int::OfNat(0) <= ({e}) * ({e})) = linarith::nlin_int_sq({e}); \
                 let __nlin_t{j}: (({e}) * ({e}) = {}) = ring; ",
                integral_form_source(&form, false, &alias)?
            ));
            args.extend([format!("__nlin_s{j}"), format!("__nlin_t{j}")]);
        }
        Ok(())
    }

    /// The sides as read, for a refusal.
    fn shown(&self, elab: &Elaborator, cx: &Cx) -> Vec<String> {
        self.sides
            .iter()
            .map(|(tm, nat, form, _)| {
                let written = elab.spell_term_clean(cx, tm).unwrap_or_else(|| elab.display_rough_term(cx, tm, &[]));
                let read = if *nat { self.nats.render(form) } else { self.ints.render(form) };
                format!("`{written}` as `{read}`")
            })
            .collect()
    }
}

fn parse_ty(source: &str) -> Result<heather_syntax::Ty, String> {
    let wrapper = format!("theorem __linarith_generated(): {source} {{ 0 }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("internal: a carrier type did not parse".into());
    };
    Ok(decl.result)
}

fn parse_expr(source: &str) -> Result<Expr, String> {
    let wrapper = format!("theorem __linarith_generated(): 0 = 0 {{ {source} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated `linarith` certificate did not parse as a theorem".into());
    };
    Ok(*decl.body.result)
}

/// Restores the certificate depth on drop.
struct Depth<'a>(&'a std::cell::Cell<usize>);

impl Drop for Depth<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() - 1);
    }
}

impl Elaborator {
    /// `linarith` and `linarith(h₁, …, hₖ)` in checking position; with
    /// `nonlinear`, `nlinarith`, which multiplies the facts too
    /// (docs/nonlinear-arithmetic-design.md §4).
    pub(crate) fn elab_linarith(&self, cx: &Cx, hyps: &[Expr], goal: &Type, lvl: &Level, span: Span, nonlinear: bool) -> R<Term> {
        let err = |msg: String| ElabError::Elab { msg, span };
        let tactic = if nonlinear { "nlinarith" } else { "linarith" };
        if self.key_of("linarith::lin_finish_le").is_none() {
            return Err(err(format!("`{tactic}` requires its certificate library; add `import linarith;`")));
        }
        // A conjunction goal, or a definition that unfolds to one
        // (`AbsLe(z, e)`), is proved side by side, each side by the same
        // call (docs/linarith-design.md §9).
        if let Some(conj) = conjunction_of(self, cx, goal, span) {
            return self.linarith_conjunction(cx, hyps, goal, &conj, lvl, span, nonlinear);
        }
        // Each written fact, split into its conjuncts (`fact_parts`).
        let mut written = Vec::new();
        let mut written_parts: Vec<(usize, String, Term, Type, Level)> = Vec::new();
        for (i, hyp) in hyps.iter().enumerate() {
            let (term, ty, level) = self.elab_infer(cx, hyp)?;
            let name = match &hyp.kind {
                heather_syntax::ExprKind::Var(name) => name.clone(),
                _ => format!("hypothesis {}", i + 1),
            };
            let mut parts = Vec::new();
            fact_parts(self, cx, name, term.clone(), ty.clone(), level.clone(), span, &mut parts);
            written_parts.extend(parts.into_iter().map(|(name, term, ty, level)| (i, name, term, ty, level)));
            written.push((term, ty, level));
        }
        // The reading and the certificate name `ring`'s and this library's
        // lemmas, which a client that imports only `linarith` does not see
        // (`resolve_declared_kinds`' overlay).
        self.scope.ring_depth.set(self.scope.ring_depth.get() + 1);
        let _depth = Depth(&self.scope.ring_depth);
        let source_cx = crate::omega_cert::source_context(cx);
        let cx = source_cx.as_ref();
        let spell = |ty: &Type| self.spell_type_clean(cx, ty).unwrap_or_else(|| self.display_type(cx, ty));
        let shown_goal = spell(goal);
        let written_name = |i: usize| match &hyps[i].kind {
            heather_syntax::ExprKind::Var(name) => name.clone(),
            _ => format!("hypothesis {}", i + 1),
        };
        // The certificate lemmas' constraint is `OrderedField + CommRingOfInt`,
        // one dictionary assembled at the carrier from its two instances
        // (issues/constraints-sharing-indices.md), so both have to be there;
        // or a class carrier (`ClassField`), whose integers are put in scope.
        let classes = [self.key_of("ordered_field::OrderedField"), self.key_of("semiring::CommRingOfInt")];
        let supported = |carrier: &Type| match self.carrier_of_ty(cx, carrier, span) {
            Some(key) => classes.iter().all(|class| {
                class.as_ref().is_some_and(|class| !self.traits.instances_answering(class, Some(&key.key)).is_empty())
            }),
            None => ClassField::of(self, cx, carrier).is_some(),
        };
        // The carrier: the goal's, else the first written fact's, else the
        // first context fact's that is at a supported carrier. `Int` and
        // `Nat` go to `omega` with `ring`'s monomials as atoms (design §8);
        // an ordered field is asked first, since its order unfolds to one
        // at `Int`.
        let goal_reading = Reading::of(self, cx, goal, span);
        let context: Vec<(String, Type)> = local_facts(self, cx);
        let at_field = |ty: &Type| Reading::of(self, cx, ty, span).is_some_and(|r| supported(&r.stated().carrier));
        let integral = |ty: &Type| crate::omega_cert::integral_sides(self, cx, ty).is_some();
        let route = if at_field(goal) {
            false
        } else if integral(goal) {
            true
        } else {
            let mut facts: Vec<&Type> = written_parts.iter().map(|part| &part.3).collect();
            if facts.is_empty() {
                facts = context.iter().map(|(_, ty)| ty).collect();
            }
            facts.into_iter().find_map(|ty| if at_field(ty) { Some(false) } else { integral(ty).then_some(true) }).unwrap_or(false)
        };
        if route {
            return self.linarith_integral(cx, &written_parts, &context, goal, lvl, span, nonlinear);
        }
        let carrier = goal_reading
            .as_ref()
            .map(|r| (Rc::clone(&r.stated().carrier), r.stated().level.clone()))
            .or_else(|| {
                written_parts
                    .iter()
                    .map(|part| &part.3)
                    .chain(context.iter().map(|(_, ty)| ty))
                    .filter_map(|ty| Reading::of(self, cx, ty, span))
                    .map(|r| (Rc::clone(&r.stated().carrier), r.stated().level.clone()))
                    .find(|(c, _)| supported(c))
            });
        let Some((carrier_ty, carrier_level)) = carrier else {
            return Err(err(format!(
                "`linarith` proves `<`, `<=`, `≈` or `¬(a < b)` at an ordered field with `OrderedField` \
                 and `CommRingOfInt` instances, or any goal from contradictory facts there; the goal is `{shown_goal}`"
            )));
        };
        let carrier_shown = spell(&carrier_ty);
        if !supported(&carrier_ty) {
            return Err(err(format!(
                "`linarith` needs `OrderedField` and `CommRingOfInt` instances at `{carrier_shown}` (the order laws its \
                 certificate is checked against, and the carrier's numerals as coefficients)"
            )));
        }
        let Some(reading) = FieldReading::at(self, cx, &carrier_ty, carrier_level.clone(), span) else {
            return Err(err(format!("`linarith` could not read `{carrier_shown}` as a ring with its integers named")));
        };
        let class_field = match self.carrier_of_ty(cx, &carrier_ty, span) {
            Some(_) => None,
            None => ClassField::of(self, cx, &carrier_ty),
        };
        let mut problem = Problem {
            carrier: reading.carrier_source().to_string(),
            spell: Spell { class: class_field.as_ref().map(|_| reading.carrier_source().to_string()) },
            reading,
            carrier_ty: Rc::clone(&carrier_ty),
            carrier_level,
            terms: Vec::new(),
            forms: Vec::new(),
            rows: Vec::new(),
            facts: Vec::new(),
            factors: Vec::new(),
            constructed: Vec::new(),
            extras: Vec::new(),
            multiply_context: false,
            decided_lt: None,
        };
        if nonlinear && carrier_shown == "Rat" && self.key_of("rat::Rat::lt_of_not_le").is_some() {
            problem.decided_lt = Some("rat::Rat::lt_of_not_le".into());
        }
        let goal_shape = match &goal_reading {
            Some(r) if spell(&r.stated().carrier) == carrier_shown => {
                let s = r.stated();
                let a = problem.term(&s.left).map_err(|e| err(format!("`linarith` could not read the goal's left side: {e}")))?;
                let b = problem.term(&s.right).map_err(|e| err(format!("`linarith` could not read the goal's right side: {e}")))?;
                match (r, s.rel) {
                    (Reading::Stated(_), Rel::Le) => Goal::Order { a, b, strict: false },
                    (Reading::Stated(_), Rel::Lt) => Goal::Order { a, b, strict: true },
                    (Reading::Stated(_), Rel::Same) => Goal::Same { a, b },
                    (Reading::NotLt(_), _) => Goal::NotLt { a, b },
                }
            }
            _ => Goal::Absurd,
        };
        // A written fact must give at least one row; a conjunct that is no
        // relation at this carrier is passed over, as a context fact is.
        let mut read_any = vec![false; written.len()];
        for (i, name, term, ty, level) in written_parts.iter().cloned() {
            let fact = Fact {
                alias: format!("__lin_h{}", problem.facts.len()),
                term,
                ty,
                level,
                shown: name,
                written: Some(i),
                bound: false,
            };
            read_any[i] |= problem.add_fact(self, cx, fact, span);
        }
        if let Some(i) = read_any.iter().position(|read| !read) {
            return Err(err(format!(
                "`linarith` combines `<`, `<=`, `≈` and `¬(x < y)` facts at `{carrier_shown}`, and conjunctions of them; `{}` is `{}`",
                written_name(i),
                spell(&written[i].1)
            )));
        }
        problem.add_denominators(self, cx, span);
        // The written facts first; failing that, every fact in context too.
        let prove = |problem: &mut Problem| if nonlinear { problem.prove_nonlinear(&goal_shape) } else { problem.prove(&goal_shape) };
        let mut found = prove(&mut problem).map_err(err)?;
        if found.is_none() {
            let before = problem.facts.len();
            // The context's facts with their evidence, conjunctions split
            // (a projection is no name `resolve_reading` resolves), and
            // definitions that unfold to conjunctions split too.
            let mut parts = Vec::new();
            for entry in crate::omega_cert::local_fact_entries(self, cx) {
                fact_parts(self, cx, entry.name, (*entry.term).clone(), entry.ty, entry.level, span, &mut parts);
            }
            for (name, term, ty, level) in parts {
                // A written fact is already a row.
                if problem.facts.iter().any(|f| f.term == term) {
                    continue;
                }
                let fact = Fact {
                    alias: format!("__lin_h{}", problem.facts.len()),
                    term,
                    ty,
                    level,
                    shown: name,
                    written: None,
                    bound: false,
                };
                problem.add_fact(self, cx, fact, span);
            }
            if problem.facts.len() > before {
                problem.add_denominators(self, cx, span);
                problem.multiply_context = true;
                found = prove(&mut problem).map_err(err)?;
            }
        }
        let Some((source, cited)) = found else {
            // Stuck: an arm equation not yet in scope might be the missing
            // fact (docs/dependent-match-compiler-design.md §4.3.1).
            self.want_match_equations(cx);
            // An order that unfolds to one at `Int` (`Rat::Le` is a
            // cross-multiplication) may follow there with products as
            // monomials, as `ring` falls back to the unfolded equation.
            if integral(goal)
                && let Ok(proof) = self.linarith_integral(cx, &written_parts, &context, goal, lvl, span, nonlinear)
            {
                return Ok(proof);
            }
            // Each row as it was read, so an atom that was not the one the
            // author meant (a numeral read as an atom, two spellings of one
            // value) shows.
            let read: Vec<String> = problem
                .rows
                .iter()
                .map(|row| {
                    let shown = &problem.facts[row.fact].shown;
                    let relation = if row.strict { ">" } else { ">=" };
                    match problem.difference(row.lo, row.hi) {
                        Ok(form) => format!("{shown}: {} {relation} 0", problem.reading.render(&form)),
                        Err(_) => shown.clone(),
                    }
                })
                .collect();
            // The goal's difference, `b − a` for `a R b`.
            let goal_read = match goal_shape {
                Goal::Order { a, b, .. } | Goal::Same { a, b } => Some((a, b)),
                Goal::NotLt { a, b } => Some((b, a)),
                Goal::Absurd => None,
            }
            .and_then(|(a, b)| problem.difference(a, b).ok())
            .map(|form| format!("; the goal's difference reads as `{}`", problem.reading.render(&form)))
            .unwrap_or_default();
            let negation = match goal_shape {
                Goal::Absurd => "",
                _ => " and the goal's negation",
            };
            let products = if nonlinear {
                let negated = match goal_shape {
                    Goal::Order { strict: true, .. } if problem.decided_lt.is_none() => {
                        format!(", the goal's negation not among them: at `{carrier_shown}` a refutation does not prove `<`")
                    }
                    Goal::Absurd => String::new(),
                    _ => ", the goal's negation among them".into(),
                };
                format!(
                    " with the pairwise products of the written facts{negated}, and the squares the terms show; \
                     a square or product it does not try can be given as a fact (`{carrier_shown}::sq_nonneg(a - b)`)"
                )
            } else {
                let multiplies = problem.forms.iter().any(|f| f.0.keys().any(|m| m.iter().sum::<u32>() >= 2));
                let hint = if multiplies { "; `nlinarith` also multiplies the facts and tries squares" } else { "" };
                format!(" (products and other non-linear terms are atoms{hint})")
            };
            return Err(err(format!(
                "`{tactic}` could not prove `{}`: no nonnegative combination of the facts{negation} \
                 is a contradiction over `{carrier_shown}`{products}; the facts read as [{}]{goal_read}",
                resugar(&shown_goal, class_field.as_ref().map(|_| carrier_shown.as_str())),
                read.join(", ")
            )));
        };
        let mut inner = cx.clone();
        let depth = cx.names.len();
        let alias = |name: String, term: Rc<Term>, ty: Type, level: Level| {
            Rc::new(Alias {
                name,
                depth,
                term,
                ty,
                level,
                skel: None,
                spliced: None,
                shifted: Default::default(),
            })
        };
        for (i, tm) in problem.terms.iter().enumerate() {
            inner.aliases.push(alias(term_alias(i), Rc::clone(tm), (*problem.carrier_ty).clone(), problem.carrier_level.clone()));
        }
        for &f in &cited {
            let fact = &problem.facts[f];
            inner.aliases.push(alias(fact.alias.clone(), Rc::new(fact.term.clone()), fact.ty.clone(), fact.level.clone()));
        }
        // At a class carrier the lemmas' dictionary is assembled from the
        // section's ordered field and the integers every ring has, put in
        // scope here (issues/constraints-sharing-indices.md).
        if let Some(field) = &class_field {
            inner = self
                .class_dictionary_scope(
                    &inner,
                    &problem.carrier,
                    CLASS_FIELD,
                    (&field.ints, &field.ty, &field.level),
                    "semiring::CommRingOfInt",
                    "semiring::CommRing",
                )
                .ok_or_else(|| err(format!("`{tactic}` could not put `{carrier_shown}`'s integers in scope")))?;
        }
        let expr = parse_expr(&source)
            .map_err(|detail| err(format!("`{tactic}` wrote a certificate that does not parse: {detail}\n  generated: {source}")))?;
        let proof = self.generated_scope(|me| me.elab_check(&inner, &expr, goal, lvl)).map_err(|error| {
            err(format!("{error}\n  generated `{tactic}` certificate: {source}"))
        })?;
        // A written fact the certificate does not cite still faces the
        // kernel, as `ring`'s do.
        let used: Vec<usize> = cited.iter().filter_map(|&f| problem.facts[f].written).collect();
        let unused = written
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !used.contains(i))
            .map(|(_, (term, ty, level))| LetValue::new(Rc::new(term), ty, level))
            .collect();
        Ok(LetValue::discard_around(self, cx, unused, proof, goal, lvl))
    }
}

impl Elaborator {
    /// A conjunction goal (`conj`, `goal` itself or what its head unfolds
    /// to), each side proved by the call that met it, and paired. A side the
    /// call cannot prove is named as a side of the goal as written, whose
    /// spelling the unfolded side may not have (a class carrier's `-e` is a
    /// projection of its parent's dictionary there).
    #[allow(clippy::too_many_arguments)]
    fn linarith_conjunction(&self, cx: &Cx, hyps: &[Expr], goal: &Type, conj: &Type, lvl: &Level, span: Span, nonlinear: bool) -> R<Term> {
        let tactic = if nonlinear { "nlinarith" } else { "linarith" };
        let err = |msg: String| ElabError::Elab { msg, span };
        let sides = self
            .display_tag_of(conj)
            .and_then(|ind| self.display_targs(cx, conj, &ind, 0))
            .filter(|sides| sides.len() == 2)
            .ok_or_else(|| err(format!("`{tactic}` could not read the two sides of the conjunction it was asked to prove")))?;
        let shown = resugar(&self.spell_type_clean(cx, goal).unwrap_or_else(|| self.display_type(cx, goal)), None);
        let prefix = format!("`{tactic}` could not prove `");
        let mut inner = cx.clone();
        let depth = cx.names.len();
        for ((side_ty, side_level), which) in sides.into_iter().zip(["left", "right"]) {
            let proof = self.elab_linarith(cx, hyps, &side_ty, &side_level, span, nonlinear).map_err(|e| match e {
                ElabError::Elab { msg, span } if msg.starts_with(&prefix) => {
                    let rest = &msg[prefix.len()..];
                    let (side_shown, rest) = rest.split_once('`').unwrap_or(("", rest));
                    // The side's own spelling, unless it shows the
                    // elaborator's placeholders.
                    let side_shown = resugar(side_shown, None);
                    let side_shown = if side_shown.is_empty() || side_shown.contains('#') || side_shown.contains('@') {
                        String::new()
                    } else {
                        format!(" `{side_shown}`")
                    };
                    ElabError::Elab { msg: format!("`{tactic}` could not prove the {which} side{side_shown} of `{shown}`{rest}"), span }
                }
                e => e,
            })?;
            inner.aliases.push(Rc::new(Alias {
                name: format!("__lin_and_{which}"),
                depth,
                term: Rc::new(proof),
                ty: side_ty,
                level: side_level,
                skel: None,
                spliced: None,
                shifted: Default::default(),
            }));
        }
        let expr = parse_expr("logic::And(left := __lin_and_left, right := __lin_and_right)")
            .map_err(|detail| err(format!("`{tactic}` could not write its conjunction: {detail}")))?;
        self.generated_scope(|me| me.elab_check(&inner, &expr, conj, lvl))
    }
}

impl Elaborator {
    /// `linarith` at `Int` and `Nat` (design §8): every side of the goal
    /// and of the facts read by `ring`'s reifier, each side that multiplies
    /// stated equal to its normal form over monomials, and `omega` given
    /// the facts and those equations. A product's normal form is spelled
    /// one way, so `omega`, which reads each product as an atom, meets
    /// `b * a`, `a * b` and the `a * b` inside `(a + 1) * b` as one.
    /// `omega` decides: the integers' rounding and its own reading of the
    /// context come with it.
    #[allow(clippy::too_many_arguments)]
    fn linarith_integral(
        &self,
        cx: &Cx,
        written: &[(usize, String, Term, Type, Level)],
        context: &[(String, Type)],
        goal: &Type,
        lvl: &Level,
        span: Span,
        nonlinear: bool,
    ) -> R<Term> {
        let err = |msg: String| ElabError::Elab { msg, span };
        let tactic = if nonlinear { "nlinarith" } else { "linarith" };
        let spell = |ty: &Type| self.spell_type_clean(cx, ty).unwrap_or_else(|| self.display_type(cx, ty));
        let carrier = |source: &str| -> R<(Type, Level)> {
            let ty = parse_ty(source).map_err(err)?;
            self.generated_scope(|me| me.elab_ty(cx, &ty))
        };
        let (int_ty, int_level) = carrier("int::Int")?;
        let (nat_ty, nat_level) = carrier("Nat")?;
        let mut problem = Integral {
            ints: FieldReading::integral(self, cx, false, int_ty.clone(), int_level.clone(), span),
            nats: FieldReading::integral(self, cx, true, nat_ty.clone(), nat_level.clone(), span),
            sides: Vec::new(),
            facts: Vec::new(),
            defs: Vec::new(),
            nonlinear,
            orders: Vec::new(),
            refute: None,
        };
        problem.sides_of(self, cx, goal);
        if nonlinear {
            problem.refute = problem.refutation(self, cx, goal);
        }
        // Each written fact's conjuncts (`fact_parts`); a fact must give at
        // least one that reads.
        let mut unread: Vec<(usize, &str, &Type)> = Vec::new();
        for (k, (i, shown, term, ty, level)) in written.iter().enumerate() {
            if !problem.sides_of(self, cx, ty) {
                unread.push((*i, shown, ty));
                continue;
            }
            let alias = format!("__lin_h{k}");
            problem.definition(self, cx, ty, &alias);
            if nonlinear && let Some(order) = problem.order_of(self, cx, ty, &alias) {
                problem.orders.push(order);
            }
            problem.facts.push(Fact {
                alias,
                term: term.clone(),
                ty: ty.clone(),
                level: level.clone(),
                shown: shown.clone(),
                written: Some(*i),
                bound: false,
            });
        }
        if let Some((_, shown, ty)) = unread.iter().find(|(i, _, _)| !problem.facts.iter().any(|f| f.written == Some(*i))) {
            return Err(err(format!(
                "`linarith` at `Int` and `Nat` combines `<`, `<=` and `=` facts there, their negations, and conjunctions of \
                 them; `{shown}` is `{}`",
                spell(ty)
            )));
        }
        let attempt = |problem: &Integral| -> Result<Term, (ElabError, String)> {
            let source = problem.source().map_err(|e| (err(e), String::new()))?;
            let mut inner = cx.clone();
            let depth = cx.names.len();
            let mut alias = |name: String, term: Rc<Term>, ty: &Type, level: &Level| {
                inner.aliases.push(Rc::new(Alias {
                    name,
                    depth,
                    term,
                    ty: ty.clone(),
                    level: level.clone(),
                    skel: None,
                    spliced: None,
                    shifted: Default::default(),
                }));
            };
            let at = |nat: bool| if nat { (&nat_ty, &nat_level) } else { (&int_ty, &int_level) };
            for (i, (tm, nat, _, _)) in problem.sides.iter().enumerate() {
                let (ty, level) = at(*nat);
                alias(term_alias(i), Rc::clone(tm), ty, level);
            }
            for (nat, reading) in [(false, &problem.ints), (true, &problem.nats)] {
                let (ty, level) = at(nat);
                for (j, tm) in reading.atom_terms().into_iter().enumerate() {
                    alias(integral_alias(nat, j), tm, ty, level);
                }
            }
            for fact in &problem.facts {
                alias(fact.alias.clone(), Rc::new(fact.term.clone()), &fact.ty, &fact.level);
            }
            let expr = parse_expr(&source).map_err(|detail| {
                (err(format!("`linarith` wrote a certificate that does not parse: {detail}\n  generated: {source}")), source.clone())
            })?;
            self.generated_scope(|me| me.elab_check(&inner, &expr, goal, lvl)).map_err(|error| (error, source))
        };
        // The written facts' sides first; failing that, the context facts'
        // too, which `omega` reads anyway but not their products. An
        // attempt that asked for a restart is discarded whatever it returns.
        let mut outcome = attempt(&problem);
        if outcome.is_err() && !self.attempt.goal_arena.restart_requested() {
            let products = problem.sides.iter().filter(|side| side.3).count();
            let orders = problem.orders.len();
            for (name, ty) in context {
                problem.sides_of(self, cx, ty);
                // A context fact is multiplied only while the products stay
                // few; a written one is already an order.
                if nonlinear
                    && problem.orders.len() < MAX_PRODUCT_ROWS
                    && !written.iter().any(|(_, _, _, wty, _)| wty == ty)
                    && let Some(order) = problem.order_of(self, cx, ty, name)
                {
                    problem.orders.push(order);
                }
            }
            if problem.sides.iter().filter(|side| side.3).count() > products || problem.orders.len() > orders {
                outcome = attempt(&problem);
            }
        }
        outcome.map_err(|(error, source)| {
            // `omega`'s verdict, not its table of what it read.
            let message = error.to_string();
            let first = message.lines().next().unwrap_or_default();
            let first = first.split("; ").next().unwrap_or_default();
            err(format!(
                "`{tactic}` could not prove `{}` at `Int`/`Nat`: `omega` found no proof with `ring`'s monomials as \
                 atoms; the sides read as [{}]\n  omega: {first}\n  generated `{tactic}` certificate: {source}",
                spell(goal),
                problem.shown(self, cx).join(", ")
            ))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(coeffs: &[(usize, Z)], constant: Z, strict: bool, index: usize, n: usize) -> FmRow {
        let mut map = BTreeMap::new();
        for (atom, c) in coeffs {
            let mut m = vec![0; atom + 1];
            m[*atom] = 1;
            map.insert(m, *c);
        }
        let mut origin = vec![0; n];
        origin[index] = 1;
        FmRow { coeffs: map, constant, strict, origin }
    }

    #[test]
    fn placeholders_read_back_as_operators() {
        let spelled = "#op<=@0_2(#constraint0.unit, #op+@0_3(#op*@0_4(d, d), #constraint0.unit))";
        assert_eq!(super::resugar(spelled, Some("K")), "K.unit <= d * d + K.unit");
        assert_eq!(super::resugar("#op*@0_4(#op+@0_3(a, b), c)", None), "(a + b) * c");
        assert_eq!(super::resugar("#op+@0_3(a, #op+@0_3(b, c))", None), "a + (b + c)");
        assert_eq!(super::resugar("AbsLe(z, #op+@0_3(e, z))", None), "AbsLe(z, e + z)");
        assert_eq!(super::resugar("f(x, y) <= g(#op+@0_3(x, y))", None), "f(x, y) <= g(x + y)");
    }

    #[test]
    fn a_chain_of_bounds_is_contradictory() {
        // x - y ≥ 0, y - z > 0, z - x ≥ 0: their sum is 0 > 0.
        let rows = vec![
            row(&[(0, 1), (1, -1)], 0, false, 0, 3),
            row(&[(1, 1), (2, -1)], 0, true, 1, 3),
            row(&[(2, 1), (0, -1)], 0, false, 2, 3),
        ];
        assert_eq!(eliminate(rows).unwrap(), Some(vec![1, 1, 1]));
    }

    #[test]
    fn scaled_rows_combine_with_positive_multipliers() {
        // 2x - 1 ≥ 0 and -3x + 1 ≥ 0: 3·first + 2·second is -1 ≥ 0.
        let rows = vec![row(&[(0, 2)], -1, false, 0, 2), row(&[(0, -3)], 1, false, 1, 2)];
        assert_eq!(eliminate(rows).unwrap(), Some(vec![3, 2]));
    }

    #[test]
    fn scaling_reads_the_reciprocal_times_its_denominator_as_one() {
        // Atoms a = 0, b = 1, r = 2, d = 3: (a·r − b)·d is a − b·d.
        let m = |atoms: &[usize]| atoms.iter().fold(Vec::new(), |acc, a| FieldReading::monomial_product(&acc, &FieldReading::atom_monomial(*a)).unwrap());
        let form: Linear = (BTreeMap::from([(m(&[0, 2]), 1), (m(&[1]), -1)]), 0);
        let factor = Factor { recip: 2, form: (BTreeMap::from([(m(&[3]), 1)]), 0), source: String::new(), proof: String::new(), fact: 0 };
        assert_eq!(scale(&form, &factor).unwrap(), (BTreeMap::from([(m(&[0]), 1), (m(&[1, 3]), -1)]), 0));
        // A constant is multiplied by the denominator, here d + 1.
        let factor = Factor { form: (BTreeMap::from([(m(&[3]), 1)]), 1), ..factor };
        assert_eq!(scale(&(BTreeMap::new(), 2), &factor).unwrap(), (BTreeMap::from([(m(&[3]), 2)]), 2));
    }

    #[test]
    fn consistent_rows_have_no_combination() {
        let rows = vec![row(&[(0, 1), (1, -1)], 0, false, 0, 2), row(&[(1, 1)], 5, true, 1, 2)];
        assert_eq!(eliminate(rows).unwrap(), None);
    }
}
