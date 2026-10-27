//! `linarith`: linear arithmetic at an ordered field, read at the field's
//! setoid equality (`docs/linarith-design.md`,
//! `issues/linarith-ordered-fields.md`).
//!
//! The tactic is an untrusted searcher in front of
//! `lib/std/tactic/linarith.hthr`. It reads the goal and the facts — the
//! written ones, then the context's — as `<`, `<=` and `≈` at one carrier
//! with an `OrderedFieldOfInt` instance (`Rat`, `CReal`), each side a linear
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

/// `ty` as the carrier's designated `≈`, `<` or `<=`, read as written.
fn stated(elab: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Stated> {
    let relation = Relation::of_type(elab, cx, ty, span)?;
    let carrier = elab.carrier_of_ty(cx, &relation.carrier, span)?;
    let Type::El { tm, .. } = ty else {
        return None;
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

/// What a fact or goal says, or its negation `¬(left < right)`.
enum Reading {
    Stated(Stated),
    NotLt(Stated),
}

impl Reading {
    fn of(elab: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Reading> {
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
}

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
    carrier_ty: Rc<Type>,
    carrier_level: Level,
    terms: Vec<Rc<Term>>,
    forms: Vec<Linear>,
    rows: Vec<Row>,
    facts: Vec<Fact>,
    factors: Vec<Factor>,
    /// The reciprocals whose positivity by construction is a fact already.
    constructed: Vec<usize>,
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
                self.add_fact(elab, cx, Fact { alias, term, ty, level, shown, written: None }, span);
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
                let source = format!("({} + -{})", term_alias(row.hi), term_alias(row.lo));
                let base = self.part(row);
                if diff == form {
                    found = Some(Factor { recip, form: form.clone(), source, proof: base, fact: row.fact });
                    break;
                }
                if diff == alone && found.is_none() {
                    let td = term_alias(d);
                    let proof = format!(
                        "{{ let __lin_d: ({source} * {td} ≈ 1) = ring; linarith::lin_den_pos<{c}>({source}, {td}, {base}, __lin_d) }}"
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
        let mut out = vec![Use { row, by: Vec::new(), form, strict }];
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
                    out.push(Use { row, by, form, strict });
                }
            }
            next += 1;
        }
        Ok(out)
    }

    /// Every fact's row with its scalings.
    fn fact_uses(&self) -> Result<Vec<Use>, String> {
        let mut out = Vec::new();
        for (i, row) in self.rows.iter().enumerate() {
            out.extend(self.uses(Some(i), self.difference(row.lo, row.hi)?, row.strict)?);
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
        let point = term_alias(a);
        let num_pos = |k: Z| format!("linarith::lin_num_pos<{c}>({point}, {})", k - 1);
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
            let Some(i) = u.row else {
                multiplier.push(match (u.by.is_empty(), k) {
                    (true, _) => (format!("{k}"), num_pos(k)),
                    (false, 1) => self.product(&u.by),
                    (false, _) => {
                        let (e, p) = self.product(&u.by);
                        (format!("({k} * {e})"), format!("linarith::lin_scale_lt<{c}>({k}, {e}, {}, {p})", num_pos(k)))
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
            let mut part = (format!("({} + -{})", term_alias(row.hi), term_alias(row.lo)), self.part(row));
            if !u.by.is_empty() {
                let (e, p) = self.product(&u.by);
                part = (format!("({e} * {})", part.0), format!("linarith::{scale_lemma}<{c}>({e}, {}, {p}, {})", part.0, part.1));
            }
            if k != 1 {
                part = (format!("{k} * {}", part.0), format!("linarith::{scale_lemma}<{c}>({k}, {}, {}, {})", part.0, num_pos(k), part.1));
            }
            parts.push((part.0, part.1, row.strict));
        }
        let constant = -sum.1;
        if constant > 0 {
            parts.push((format!("{constant}"), num_pos(constant), true));
        }
        let (s, hs, positive) = match parts.pop() {
            None => ("0".to_string(), format!("linarith::lin_zero_le<{c}>({point})"), false),
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
                "logic::false_elim({{ let {name}: ({s} ≈ 0) = ring; linarith::lin_finish_false<{c}>({s}, {hs}, {name}) }})"
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
                format!(
                    "{{ let {name}: ({k} * ({tb} + -{ta}) ≈ {s}) = ring; linarith::{finish}<{c}>({ta}, {tb}, {k}, {s}, {hk}, {hs}, {name}) }}"
                )
            }
        };
        Ok((source, cited))
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
    /// `linarith` and `linarith(h₁, …, hₖ)` in checking position.
    pub(crate) fn elab_linarith(&self, cx: &Cx, hyps: &[Expr], goal: &Type, lvl: &Level, span: Span) -> R<Term> {
        let err = |msg: String| ElabError::Elab { msg, span };
        if self.key_of("linarith::lin_finish_le").is_none() {
            return Err(err("`linarith` requires its certificate library; add `import linarith;`".into()));
        }
        let mut written = Vec::new();
        for hyp in hyps {
            written.push(self.elab_infer(cx, hyp)?);
        }
        // The reading and the certificate name `ring`'s and this library's
        // lemmas, which a client that imports only `linarith` does not see
        // (`resolve_declared_kinds`' overlay).
        self.ring_depth.set(self.ring_depth.get() + 1);
        let _depth = Depth(&self.ring_depth);
        let source_cx = crate::omega_cert::source_context(cx);
        let cx = source_cx.as_ref();
        let spell = |ty: &Type| self.spell_type_clean(cx, ty).unwrap_or_else(|| self.display_type(cx, ty));
        let shown_goal = spell(goal);
        let written_name = |i: usize| match &hyps[i].kind {
            heather_syntax::ExprKind::Var(name) => name.clone(),
            _ => format!("hypothesis {}", i + 1),
        };
        let class = self.key_of("ordered_field::OrderedFieldOfInt");
        let supported = |carrier: &Type| {
            let Some(class) = &class else { return false };
            self.carrier_of_ty(cx, carrier, span)
                .is_some_and(|key| !self.traits.instances_answering(class, Some(&key.key)).is_empty())
        };
        // The carrier: the goal's, else the first written fact's, else the
        // first context fact's that is at a supported carrier.
        let goal_reading = Reading::of(self, cx, goal, span);
        let context: Vec<(String, Type)> = local_facts(self, cx);
        let carrier = goal_reading
            .as_ref()
            .map(|r| (Rc::clone(&r.stated().carrier), r.stated().level.clone()))
            .or_else(|| {
                written
                    .iter()
                    .map(|(_, ty, _)| ty)
                    .chain(context.iter().map(|(_, ty)| ty))
                    .filter_map(|ty| Reading::of(self, cx, ty, span))
                    .map(|r| (Rc::clone(&r.stated().carrier), r.stated().level.clone()))
                    .find(|(c, _)| supported(c))
            });
        let Some((carrier_ty, carrier_level)) = carrier else {
            return Err(err(format!(
                "`linarith` proves `<`, `<=`, `≈` or `¬(a < b)` at an ordered field with an `OrderedFieldOfInt` \
                 instance, or any goal from contradictory facts there; the goal is `{shown_goal}`"
            )));
        };
        let carrier_shown = spell(&carrier_ty);
        if !supported(&carrier_ty) {
            return Err(err(format!(
                "`linarith` needs an `OrderedFieldOfInt` instance at `{carrier_shown}` (the order laws its \
                 certificate is checked against, and the carrier's numerals as coefficients)"
            )));
        }
        let Some(reading) = FieldReading::at(self, cx, &carrier_ty, carrier_level.clone(), span) else {
            return Err(err(format!("`linarith` could not read `{carrier_shown}` as a ring with its integers named")));
        };
        let mut problem = Problem {
            carrier: reading.carrier_source().to_string(),
            reading,
            carrier_ty: Rc::clone(&carrier_ty),
            carrier_level,
            terms: Vec::new(),
            forms: Vec::new(),
            rows: Vec::new(),
            facts: Vec::new(),
            factors: Vec::new(),
            constructed: Vec::new(),
        };
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
        for (i, (term, ty, level)) in written.iter().enumerate() {
            let fact = Fact {
                alias: format!("__lin_h{}", problem.facts.len()),
                term: term.clone(),
                ty: ty.clone(),
                level: level.clone(),
                shown: written_name(i),
                written: Some(i),
            };
            if !problem.add_fact(self, cx, fact, span) {
                return Err(err(format!(
                    "`linarith` combines `<`, `<=`, `≈` and `¬(x < y)` facts at `{carrier_shown}`; `{}` is `{}`",
                    written_name(i),
                    spell(ty)
                )));
            }
        }
        problem.add_denominators(self, cx, span);
        // The written facts first; failing that, every fact in context too.
        let mut found = problem.prove(&goal_shape).map_err(err)?;
        if found.is_none() {
            let before = problem.facts.len();
            for (name, _) in &context {
                let Ok((term, ty, level)) = self.resolve_reading(cx, name, span) else {
                    continue;
                };
                // A written fact is already a row.
                if problem.facts.iter().any(|f| f.term == term) {
                    continue;
                }
                let fact = Fact {
                    alias: format!("__lin_h{}", problem.facts.len()),
                    term,
                    ty,
                    level,
                    shown: name.clone(),
                    written: None,
                };
                problem.add_fact(self, cx, fact, span);
            }
            if problem.facts.len() > before {
                problem.add_denominators(self, cx, span);
                found = problem.prove(&goal_shape).map_err(err)?;
            }
        }
        let Some((source, cited)) = found else {
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
            return Err(err(format!(
                "`linarith` could not prove `{shown_goal}`: no nonnegative combination of the facts{negation} \
                 is a contradiction over `{carrier_shown}` (products and other non-linear terms are atoms); \
                 the facts read as [{}]{goal_read}",
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
        let expr = parse_expr(&source)
            .map_err(|detail| err(format!("`linarith` wrote a certificate that does not parse: {detail}\n  generated: {source}")))?;
        let proof = self.generated_scope(|me| me.elab_check(&inner, &expr, goal, lvl)).map_err(|error| {
            err(format!("{error}\n  generated `linarith` certificate: {source}"))
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
