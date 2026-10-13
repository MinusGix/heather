//! `ring`: commutative-ring normalization by reflection
//! (`docs/ring-normalization-design.md`, `issues/ring-normalization.md`).
//!
//! The tactic is an untrusted reifier in front of `lib/std/ring.hthr`. It
//! reads an equation at `Int` or `Nat` into `RingExpr`/`RingNat` syntax over
//! an atom list and writes one application of `RingExpr::sound` (or
//! `RingNat::sound`) whose `refl` the kernel checks by evaluating the
//! in-language normalizer. With hypotheses `ring(h₁, …, hₖ)` it also searches
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
use heather_syntax::{Expr, Item, Span, parse_file};

use crate::context::Alias;
use crate::omega_cert::{integer_source, named_args};
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

/// How deep projections are read through (`(x + y).num` reads `x + y`'s
/// numerator, which may read another).
const PROJECTION_DEPTH: u32 = 8;

/// Multiplier search bounds: closure rounds, and the most unknowns the linear
/// system may have.
const SEARCH_ROUNDS: usize = 4;
const SEARCH_CANDIDATES: usize = 240;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Carrier {
    Int,
    Nat,
}

impl Carrier {
    fn name(self) -> &'static str {
        match self {
            Carrier::Int => "Int",
            Carrier::Nat => "Nat",
        }
    }
}

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
    source: String,
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

struct Reifier<'a> {
    elab: &'a Elaborator,
    cx: &'a Cx,
    carrier: Carrier,
    ty: Type,
    level: Level,
    atoms: Vec<Atom>,
}

impl Reifier<'_> {
    fn reify(&mut self, tm: &Rc<Term>) -> Result<Syn, String> {
        self.reify_within(tm, PROJECTION_DEPTH)
    }

    fn reify_within(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Syn, String> {
        match self.carrier {
            Carrier::Int => self.reify_int(tm, depth),
            Carrier::Nat => self.reify_nat(tm, depth),
        }
    }

    fn binary(&mut self, tm: &Rc<Term>, name: &str, depth: u32) -> Result<Option<(Syn, Syn)>, String> {
        let Some(args) = named_args(self.elab, tm, name) else {
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
        self.projection_or_atom(tm, depth)
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

    /// A field read off a value that computes to a constructor is read as the
    /// field: `Rat::add(x, y).num` is the numerator `add` builds. Anything
    /// else is an atom.
    fn projection_or_atom(&mut self, tm: &Rc<Term>, depth: u32) -> Result<Syn, String> {
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
        let mut path = Vec::new();
        let mut cur = tm;
        while let Some((first, pair)) = crate::spelling::proj_of(cur) {
            path.push(first);
            cur = pair;
        }
        if path.is_empty() || !matches!(app_spine(cur).0, Term::GlobalTm { .. }) {
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
    /// somewhere computation could reach (`(x + y).den.int()` against
    /// `x.den.mul(y.den).int()`).
    fn intern(&mut self, tm: &Rc<Term>) -> Result<usize, String> {
        if let Some(index) = self.atoms.iter().position(|atom| atom.term == *tm) {
            return Ok(index);
        }
        let source = self
            .elab
            .spell_term_source(self.cx, tm)
            .ok_or_else(|| format!("`ring` could not spell one of the {} atoms as source", self.carrier.name()))?;
        if let Some(index) = self.atoms.iter().position(|atom| atom.source == source) {
            return Ok(index);
        }
        if let Some(index) = self.convertible(tm) {
            return Ok(index);
        }
        self.atoms.push(Atom {
            term: Rc::clone(tm),
            source,
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
// Rendering the certificate.

fn int_source(value: Z) -> String {
    if value >= 0 {
        format!("int::OfNat({value})")
    } else {
        format!("int::NegSucc({})", value.unsigned_abs() - 1)
    }
}

fn syn_source(syn: &Syn, carrier: Carrier) -> String {
    let (atom, konst, add, mul) = match carrier {
        Carrier::Int => ("ring::RAtom", "ring::RConst", "ring::RAdd", "ring::RMul"),
        Carrier::Nat => ("ring::NAtom", "ring::NConst", "ring::NAdd", "ring::NMul"),
    };
    match syn {
        Syn::Atom(i) => format!("{atom}({i})"),
        Syn::Const(c) => match carrier {
            Carrier::Int => format!("{konst}({})", int_source(*c)),
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
    carrier: Carrier,
    /// Hypotheses the combination uses, by their index among the written ones.
    used: Vec<usize>,
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
) -> Result<Certificate, String> {
    let shown = elab
        .spell_type_clean(cx, goal)
        .unwrap_or_else(|| elab.display_type(cx, goal));
    let Some(goal_eq) = equation(elab, cx, goal) else {
        return Err(format!("`ring` proves an equation at `Int` or `Nat`; the goal is `{shown}`"));
    };
    let mut reifier = Reifier {
        elab,
        cx,
        carrier: goal_eq.carrier,
        ty: goal_eq.ty.clone(),
        level: goal_eq.level.clone(),
        atoms: Vec::new(),
    };
    let goal_syn = Written {
        lhs: reifier.reify(&goal_eq.lhs)?,
        rhs: reifier.reify(&goal_eq.rhs)?,
    };
    let mut hyp_syn = Vec::new();
    for (name, ty) in hyps {
        let spelled = elab.spell_type_clean(cx, ty).unwrap_or_else(|| elab.display_type(cx, ty));
        let Some(eq) = equation(elab, cx, ty) else {
            return Err(format!("`ring` combines equations; `{name}` is `{spelled}`"));
        };
        if eq.carrier != goal_eq.carrier {
            return Err(format!(
                "`ring`: the goal is at `{}` but `{name}` is an equation at `{}`",
                goal_eq.carrier.name(),
                eq.carrier.name()
            ));
        }
        hyp_syn.push(Written {
            lhs: reifier.reify(&eq.lhs)?,
            rhs: reifier.reify(&eq.rhs)?,
        });
    }
    let carrier = goal_eq.carrier;
    let atom_sources: Vec<String> = reifier.atoms.iter().map(|a| a.source.clone()).collect();
    let target = poly_of(&goal_syn.lhs)?.sub(&poly_of(&goal_syn.rhs)?)?;
    let atoms = atom_sources
        .iter()
        .rev()
        .fold("list::Nil".to_string(), |tail, atom| format!("list::Cons({atom}, {tail})"));
    let (sound, sound_with) = match carrier {
        Carrier::Int => ("ring::RingExpr::sound", "ring::RingExpr::sound_with"),
        Carrier::Nat => ("ring::RingNat::sound", "ring::RingNat::sound_with"),
    };
    let lhs = syn_source(&goal_syn.lhs, carrier);
    let rhs = syn_source(&goal_syn.rhs, carrier);
    if target.is_zero() {
        return Ok(Certificate {
            source: format!("{sound}({ATOMS}, {lhs}, {rhs}, refl)"),
            atoms,
            carrier,
            used: Vec::new(),
        });
    }
    let residual = || render_poly(&target, &atom_sources);
    if hyps.is_empty() {
        return Err(format!(
            "`ring` could not prove `{shown}`: it is not an identity of commutative rings; \
             the two sides differ by `{}`",
            residual()
        ));
    }
    let hyp_polys = hyp_syn
        .iter()
        .map(|w| poly_of(&w.lhs)?.sub(&poly_of(&w.rhs)?))
        .collect::<Result<Vec<_>, String>>()?;
    let Some(found) = multipliers(&target, &hyp_polys)? else {
        return Err(format!(
            "`ring` could not prove `{shown}` from the given equations: no combination of them \
             (with polynomial multipliers) accounts for the difference `{}`",
            residual()
        ));
    };
    let used: Vec<usize> = (0..hyps.len()).filter(|i| !found[*i].is_zero()).collect();
    let lift = |syn: &Syn| match carrier {
        Carrier::Int => syn_source(syn, carrier),
        Carrier::Nat => format!("ring::RingNat::lift({})", syn_source(syn, carrier)),
    };
    let int_atoms = match carrier {
        Carrier::Int => ATOMS.to_string(),
        Carrier::Nat => format!("ring::RingNat::lift_atoms({ATOMS})"),
    };
    // One `cᵢ·(aᵢ − bᵢ)` per used hypothesis, summed left to right; the
    // proof that the sum is zero has the same shape.
    let mut parts = used.iter().map(|&i| {
        let c = poly_source(&found[i]);
        let (a, b) = (&hyp_syn[i].lhs, &hyp_syn[i].rhs);
        let expr = format!("ring::RMul({c}, ring::RSub({}, {}))", lift(a), lift(b));
        let proof = match carrier {
            Carrier::Int => format!(
                "ring::RingExpr::hyp({ATOMS}, {c}, {}, {}, {})",
                syn_source(a, carrier),
                syn_source(b, carrier),
                hyp_name(i)
            ),
            Carrier::Nat => format!(
                "ring::RingNat::hyp({ATOMS}, {c}, {}, {}, {})",
                syn_source(a, carrier),
                syn_source(b, carrier),
                hyp_name(i)
            ),
        };
        (expr, proof)
    });
    let (mut d, mut hd) = parts.next().expect("a nonzero target used some hypothesis");
    for (expr, proof) in parts {
        hd = format!("ring::RingExpr::hyp_add({int_atoms}, {d}, {expr}, {hd}, {proof})");
        d = format!("ring::RAdd({d}, {expr})");
    }
    Ok(Certificate {
        source: format!("{sound_with}({ATOMS}, {lhs}, {rhs}, {d}, {hd}, refl)"),
        atoms,
        carrier,
        used,
    })
}

fn hyp_name(i: usize) -> String {
    format!("__ring_h{i}")
}

fn parse_expr(source: &str) -> Result<Expr, String> {
    let wrapper = format!("theorem __ring_generated(): 0 = 0 {{ {source} }}");
    let mut file = parse_file(&wrapper).map_err(|error| error.msg)?;
    let Some(Item::Decl(decl)) = file.items.pop() else {
        return Err("the generated `ring` certificate did not parse as a theorem".into());
    };
    Ok(*decl.body.result)
}

fn parse_atom_list(literal: &str, carrier: Carrier) -> Result<(heather_syntax::Ty, Expr), String> {
    let element = match carrier {
        Carrier::Int => "int::Int",
        Carrier::Nat => "Nat",
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
        let cert = reconstruct(self, cx, goal, &named).map_err(err)?;
        self.ring_depth.set(self.ring_depth.get() + 1);
        let _depth = Depth(&self.ring_depth);
        let (list_ty, parsed) = parse_atom_list(&cert.atoms, cert.carrier)
            .map_err(|detail| err(format!("`ring` wrote an atom list that does not parse: {detail}\n  generated: {}", cert.atoms)))?;
        let checked = self.generated_scope(|me| {
            let (ty, level) = me.elab_ty(cx, &list_ty)?;
            let atoms = me.elab_check(cx, &parsed, &ty, &level)?;
            Ok((atoms, ty, level))
        });
        let (atoms, ty, level) = checked.map_err(|error: ElabError| {
            err(format!("{error}\n  generated `ring` atom list: {}", cert.atoms))
        })?;
        // As `omega`'s: one transparent slot per atom list, so the kernel
        // meets the list once rather than once per use.
        let term = match self.attempt.goal_arena.allocate_transparent(cx, ty.clone(), level.clone(), atoms.clone()) {
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
        }));
        for &i in &cert.used {
            let (term, ty, level) = &written[i];
            inner.aliases.push(Rc::new(Alias {
                name: hyp_name(i),
                depth,
                term: Rc::new(term.clone()),
                ty: ty.clone(),
                level: level.clone(),
                skel: None,
            }));
        }
        let expr = parse_expr(&cert.source)
            .map_err(|detail| err(format!("`ring` wrote a certificate that does not parse: {detail}\n  generated: {}", cert.source)))?;
        self.generated_scope(|me| me.elab_check(&inner, &expr, goal, lvl)).map_err(|error| {
            err(format!(
                "{error}\n  generated `ring` certificate: {}\n  where {ATOMS} = {}",
                cert.source, cert.atoms
            ))
        })
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
}
