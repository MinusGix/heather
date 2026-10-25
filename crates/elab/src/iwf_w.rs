//! Indexed families with a recursive **function** field: the `IWf` route's
//! surface lowered on the kernel's `W` (docs/iwf-infinitary-design.md; the
//! section numbers below are that document's).
//!
//! ```text
//! W₀          = W(x : S). P(x)                      S: the shape declaration
//! ⟦D<ā>(m)⟧   = Σ(t : W₀). El(ok t m)
//! ok(sup(a; f), j) = Σ(e : Id(I; o(a); j)). REST
//! REST        = Id(f₀; f)                                   no recursive field
//!             | CH(f)                                       one
//!             | Σ(k̄ : K̄). Σ(q : Id(ρ(k̄); f)). CH(f)          two or more
//! ```
//!
//! The declaration form, the classifier, the shape, the `match` motive (with
//! its inversion) and the recursion guard are the `IWf` route's
//! (`iwf_family.rs`); this module supplies what the kernel's `IWf` cannot
//! say, a function's worth of children. [`IwSig`] is the signature, read back
//! off the type exactly as `IWfSig` is.
//!
//! Scoping convention: an [`IwSig`] is scoped in some context `B`, and every
//! helper taking `by` builds its result `by` binders past `B`, with every term
//! argument already scoped there.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::ast::{Span, TyKind};

use crate::inductive::{FieldKind, Inductive, inject};
use crate::iwf_family::{ArmEnv, child_index, res_expr};
use crate::recursion::{FnChildIh, Guard, GuardKind};
use crate::{Alias, Cx, Elaborator, R, err};

fn var(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

/// `f a` at a head that infers its own Π.
fn app(fun: Term, arg: Term) -> Term {
    Term::AppAt {
        fun: Rc::new(fun),
        arg: Rc::new(arg),
    }
}

fn join(a: &Level, b: &Level) -> Level {
    Level::join(a.clone(), b.clone())
}

fn pi(dom_level: &Level, cod_level: &Level, dom: Type, cod: Type) -> Type {
    Type::Pi {
        dom_level: dom_level.clone(),
        cod_level: cod_level.clone(),
        dom: Rc::new(dom),
        cod: Rc::new(cod),
    }
}

fn lam(dom_level: &Level, cod_level: &Level, dom: Type, body: Term) -> Term {
    Term::Lam {
        dom_level: dom_level.clone(),
        cod_level: cod_level.clone(),
        dom: Rc::new(dom),
        body: Rc::new(body),
    }
}

fn id_ty(level: &Level, ty: Type, lhs: Term, rhs: Term) -> Type {
    Type::Id {
        level: level.clone(),
        ty: Rc::new(ty),
        lhs: Rc::new(lhs),
        rhs: Rc::new(rhs),
    }
}

fn refl(level: &Level, ty: Type, tm: Term) -> Term {
    Term::Refl {
        level: level.clone(),
        ty: Rc::new(ty),
        tm: Rc::new(tm),
    }
}

/// `Σ(_ : a). b` with `b` not depending on the first component, given in
/// the ambient scope (shifted under the binder here).
fn sigma(a: (&Type, &Level), b: (&Type, &Level)) -> Type {
    Type::Sigma {
        fst_level: a.1.clone(),
        snd_level: b.1.clone(),
        fst: Rc::new(a.0.clone()),
        snd: Rc::new(b.0.shift_local(1)),
    }
}

fn pair(a: (&Type, &Level), b: (&Type, &Level), fst: Term, snd: Term) -> Term {
    Term::Pair {
        fst_level: a.1.clone(),
        snd_level: b.1.clone(),
        fst_ty: Rc::new(a.0.clone()),
        snd_ty: Rc::new(b.0.shift_local(1)),
        fst: Rc::new(fst),
        snd: Rc::new(snd),
    }
}

fn fst_of(a: (&Type, &Level), b: (&Type, &Level), p: Term) -> Term {
    Term::Fst {
        fst_level: a.1.clone(),
        snd_level: b.1.clone(),
        fst_ty: Rc::new(a.0.clone()),
        snd_ty: Rc::new(b.0.shift_local(1)),
        pair: Rc::new(p),
    }
}

fn snd_of(a: (&Type, &Level), b: (&Type, &Level), p: Term) -> Term {
    Term::Snd {
        fst_level: a.1.clone(),
        snd_level: b.1.clone(),
        fst_ty: Rc::new(a.0.clone()),
        snd_ty: Rc::new(b.0.shift_local(1)),
        pair: Rc::new(p),
    }
}

/// The right-nested non-dependent product of `items` (at least one).
fn prod_ty(items: &[(Type, Level)]) -> (Type, Level) {
    let (last, rest) = items.split_last().expect("a product of at least one item");
    let mut acc = last.clone();
    for (t, l) in rest.iter().rev() {
        let level = join(l, &acc.1);
        acc = (sigma((t, l), (&acc.0, &acc.1)), level);
    }
    acc
}

/// The right-nested tuple of `vals` at [`prod_ty`]`(items)`.
fn tuple(items: &[(Type, Level)], vals: Vec<Term>) -> Term {
    let mut vals = vals;
    let mut acc = vals.pop().expect("a tuple of at least one value");
    for (k, v) in vals.into_iter().enumerate().rev() {
        let rest = prod_ty(&items[k + 1..]);
        acc = pair((&items[k].0, &items[k].1), (&rest.0, &rest.1), v, acc);
    }
    acc
}

/// Component `t` of a [`tuple`] at `items`.
fn proj(items: &[(Type, Level)], t: usize, tuple: Term) -> Term {
    let n = items.len();
    let mut cur = tuple;
    for s in 0..t {
        let rest = prod_ty(&items[s + 1..]);
        cur = snd_of((&items[s].0, &items[s].1), (&rest.0, &rest.1), cur);
    }
    if t + 1 < n {
        let rest = prod_ty(&items[t + 1..]);
        cur = fst_of((&items[t].0, &items[t].1), (&rest.0, &rest.1), cur);
    }
    cur
}

/// The same for codes: `Σ` codes, right-nested.
fn prod_code(items: &[(Term, Level)]) -> (Term, Level) {
    let (last, rest) = items.split_last().expect("a product of at least one item");
    let mut acc = last.clone();
    for (t, l) in rest.iter().rev() {
        let level = join(l, &acc.1);
        acc = (
            Term::TmSigma {
                fst_level: l.clone(),
                snd_level: acc.1.clone(),
                fst: Rc::new(t.clone()),
                snd: Rc::new(acc.0.shift_local(1)),
            },
            level,
        );
    }
    acc
}

fn strengthen_tm(t: &Term, by: u32) -> Option<Term> {
    let mut cur = t.clone();
    for _ in 0..by {
        let s = cur.inst_top(0, &Term::Zero);
        if s.shift_local(1) != cur {
            return None;
        }
        cur = s;
    }
    Some(cur)
}

fn strengthen_ty(t: &Type, by: u32) -> Option<Type> {
    let mut cur = t.clone();
    for _ in 0..by {
        let s = cur.inst_top(0, &Term::Zero);
        if s.shift_local(1) != cur {
            return None;
        }
        cur = s;
    }
    Some(cur)
}

/// The signature of a `W`-encoded family (§5): everything but the index.
#[derive(Clone)]
pub(crate) struct IwSig {
    pub ls: Level,
    pub lp: Level,
    /// `ls ⊔ lp`, the tree's.
    pub lw: Level,
    /// `li ⊔ lw`, the predicate's.
    pub lk: Level,
    pub ilvl: Level,
    pub ity: Rc<Type>,
    pub shape: Rc<Type>,
    /// `P`, over `(B, x : S)`.
    pub pos: Rc<Type>,
    /// `ok`, over `(B, t : W₀)`: an `elim_W` at the motive `Π(j : I). Ty lk`.
    pub ok: Rc<Term>,
}

impl IwSig {
    pub fn shift_local(&self, by: u32) -> IwSig {
        IwSig {
            ls: self.ls.clone(),
            lp: self.lp.clone(),
            lw: self.lw.clone(),
            lk: self.lk.clone(),
            ilvl: self.ilvl.clone(),
            ity: Rc::new(self.ity.shift_local(by)),
            shape: Rc::new(self.shape.shift_local(by)),
            pos: Rc::new(self.pos.shift_local_above(by, 1)),
            ok: Rc::new(self.ok.shift_local_above(by, 1)),
        }
    }

    /// `lw ⊔ lk` — the family's level.
    pub fn lvl(&self) -> Level {
        join(&self.lw, &self.lk)
    }

    /// `Π(y : P a). W₀`'s level.
    fn lf(&self) -> Level {
        join(&self.lp, &self.lw)
    }

    pub fn w0(&self, by: u32) -> Type {
        Type::W {
            shape_level: self.ls.clone(),
            pos_level: self.lp.clone(),
            shape: Rc::new(self.shape.shift_local(by)),
            pos: Rc::new(self.pos.shift_local_above(by, 1)),
        }
    }

    pub fn pos_at(&self, by: u32, label: &Term) -> Type {
        self.pos.inst_top(by, label)
    }

    /// `Π(y : P label). W₀`.
    pub fn kids_ty(&self, by: u32, label: &Term) -> Type {
        pi(&self.lp, &self.lw, self.pos_at(by, label), self.w0(by + 1))
    }

    /// `El(ok t j)`.
    pub fn ok_ty(&self, by: u32, t: &Term, j: &Term) -> Type {
        Type::El {
            level: self.lk.clone(),
            tm: Rc::new(app(self.ok.inst_top(by, t), j.clone())),
        }
    }

    /// `El(ok t m)` over `(B + by, t)`, with `m` scoped at `B + by`.
    fn ok_under(&self, by: u32, m: &Term) -> Type {
        Type::El {
            level: self.lk.clone(),
            tm: Rc::new(app(self.ok.shift_local_above(by, 1), m.shift_local(1))),
        }
    }

    /// `⟦D⟧(m) = Σ(t : W₀). El(ok t m)`.
    pub fn fam(&self, by: u32, m: &Term) -> Type {
        Type::Sigma {
            fst_level: self.lw.clone(),
            snd_level: self.lk.clone(),
            fst: Rc::new(self.w0(by)),
            snd: Rc::new(self.ok_under(by, m)),
        }
    }

    pub fn pair(&self, by: u32, m: &Term, t: Term, c: Term) -> Term {
        Term::Pair {
            fst_level: self.lw.clone(),
            snd_level: self.lk.clone(),
            fst_ty: Rc::new(self.w0(by)),
            snd_ty: Rc::new(self.ok_under(by, m)),
            fst: Rc::new(t),
            snd: Rc::new(c),
        }
    }

    pub fn fst(&self, by: u32, m: &Term, p: Term) -> Term {
        Term::Fst {
            fst_level: self.lw.clone(),
            snd_level: self.lk.clone(),
            fst_ty: Rc::new(self.w0(by)),
            snd_ty: Rc::new(self.ok_under(by, m)),
            pair: Rc::new(p),
        }
    }

    pub fn snd(&self, by: u32, m: &Term, p: Term) -> Term {
        Term::Snd {
            fst_level: self.lw.clone(),
            snd_level: self.lk.clone(),
            fst_ty: Rc::new(self.w0(by)),
            snd_ty: Rc::new(self.ok_under(by, m)),
            pair: Rc::new(p),
        }
    }

    pub fn sup(&self, by: u32, label: Term, kids: Term) -> Term {
        Term::Sup {
            shape_level: self.ls.clone(),
            pos_level: self.lp.clone(),
            shape_ty: Rc::new(self.shape.shift_local(by)),
            pos_ty: Rc::new(self.pos.shift_local_above(by, 1)),
            label: Rc::new(label),
            children: Rc::new(kids),
        }
    }

    /// `f₀ = λ(y : P label). elim_Empty(_. W₀; y)` — a leaf's children.
    fn f0(&self, by: u32, label: &Term) -> Term {
        lam(
            &self.lp,
            &self.lw,
            self.pos_at(by, label),
            Term::ElimEmpty {
                level: self.lw.clone(),
                scrut_level: self.lp.clone(),
                motive: Rc::new(self.w0(by + 2)),
                scrut: Rc::new(var(0)),
            },
        )
    }

    /// Read a family type back: the signature and the index. Context-free:
    /// it only takes the type apart. The second component being an `elim_W`
    /// over the bound tree, *applied to an index*, is what tells this
    /// encoding apart from tier 2's (`WParts::read`), whose predicate is the
    /// `elim_W` itself.
    pub(crate) fn read(ty: &Type) -> Option<(IwSig, Rc<Term>)> {
        let ty = crate::inductive::decoded(ty);
        let Type::Sigma { fst_level, snd_level, fst, snd } = &*ty else {
            return None;
        };
        let fst = crate::inductive::decoded(fst);
        let Type::W { shape_level, pos_level, shape, pos } = &*fst else {
            return None;
        };
        let Type::El { tm, .. } = &**snd else {
            return None;
        };
        let Term::AppAt { fun, arg } = &**tm else {
            return None;
        };
        let Term::ElimW { motive, scrut, .. } = &**fun else {
            return None;
        };
        if **scrut != var(0) {
            return None;
        }
        // The motive is over (B, t, w): `Π(j : I). Ty lk`.
        let Type::Pi { dom_level, dom, .. } = &**motive else {
            return None;
        };
        let ity = strengthen_ty(dom, 2)?;
        let idx = strengthen_tm(arg, 1)?;
        Some((
            IwSig {
                ls: shape_level.clone(),
                lp: pos_level.clone(),
                lw: fst_level.clone(),
                lk: snd_level.clone(),
                ilvl: dom_level.clone(),
                ity: Rc::new(ity),
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
                ok: Rc::clone(fun),
            },
            Rc::new(idx),
        ))
    }
}

/// One recursive field of a constructor, elaborated at a branch (§4).
pub(crate) struct Kid {
    /// Its position among the constructor's surface fields.
    pub field: usize,
    /// A function field's domain and its level; `None` for a plain child.
    pub dom: Option<(Type, Level)>,
    /// The written index: under the field's binder `y` for a function field.
    pub idx: Term,
}

/// One constructor's data at one base context `B`: the signature, the
/// recursive fields and the label, all scoped there.
struct Br<'a> {
    sig: IwSig,
    kids: &'a [Kid],
    lab: Term,
}

impl Br<'_> {
    fn n(&self) -> usize {
        self.kids.len()
    }

    fn lf(&self) -> Level {
        self.sig.lf()
    }

    fn dom(&self, t: usize, by: u32) -> Type {
        match &self.kids[t].dom {
            Some((a, _)) => a.shift_local(by),
            None => Type::Unit {
                level: self.sig.lp.clone(),
            },
        }
    }

    /// `A_s + (A_{s+1} + … + A_n)`.
    fn tail(&self, s: usize, by: u32) -> Type {
        if s + 1 == self.n() {
            return self.dom(s, by);
        }
        Type::Sum {
            lhs_level: self.sig.lp.clone(),
            rhs_level: self.sig.lp.clone(),
            lhs: Rc::new(self.dom(s, by)),
            rhs: Rc::new(self.tail(s + 1, by)),
        }
    }

    /// `inj_t(y) : P(label)`: the identity for one field, the `inl`/`inr`
    /// path into the right-nested sum otherwise.
    fn inj(&self, t: usize, y: Term, by: u32) -> Term {
        let n = self.n();
        if n == 1 {
            return y;
        }
        let lp = &self.sig.lp;
        let mut v = if t + 1 < n {
            Term::Inl {
                lhs_level: lp.clone(),
                rhs_level: lp.clone(),
                lhs: Rc::new(self.dom(t, by)),
                rhs: Rc::new(self.tail(t + 1, by)),
                val: Rc::new(y),
            }
        } else {
            y
        };
        for s in (0..t).rev() {
            v = Term::Inr {
                lhs_level: lp.clone(),
                rhs_level: lp.clone(),
                lhs: Rc::new(self.dom(s, by)),
                rhs: Rc::new(self.tail(s + 1, by)),
                val: Rc::new(v),
            };
        }
        v
    }

    fn lab(&self, by: u32) -> Term {
        self.lab.shift_local(by)
    }

    fn pos(&self, by: u32) -> Type {
        self.sig.pos_at(by, &self.lab(by))
    }

    fn kids_ty(&self, by: u32) -> Type {
        self.sig.kids_ty(by, &self.lab(by))
    }

    fn f0(&self, by: u32) -> Term {
        self.sig.f0(by, &self.lab(by))
    }

    /// Field `t`'s written index `by` binders past `B`, still under `y` for
    /// a function field.
    fn idx(&self, t: usize, by: u32) -> Term {
        let kid = &self.kids[t];
        match kid.dom {
            Some(_) => kid.idx.shift_local_above(by, 1),
            None => kid.idx.shift_local(by),
        }
    }

    /// `K_t`: `Π(y : A_t). W₀` for a function field, `W₀` for a plain one.
    fn k_items(&self, by: u32) -> Vec<(Type, Level)> {
        (0..self.n())
            .map(|t| match &self.kids[t].dom {
                Some(_) => (pi(&self.sig.lp, &self.sig.lw, self.dom(t, by), self.sig.w0(by + 1)), self.lf()),
                None => (self.sig.w0(by), self.sig.lw.clone()),
            })
            .collect()
    }

    /// `k_t y` (or `k_t`) out of the stored children `kbar`.
    fn k_at(&self, kbar: &Term, t: usize, y: Term, by: u32) -> Term {
        let k = proj(&self.k_items(by), t, kbar.clone());
        match &self.kids[t].dom {
            Some(_) => app(k, y),
            None => k,
        }
    }

    /// `ρ(k̄) = λp. case p of inj_t y ⇒ k_t y` (§3, two or more fields).
    fn rho(&self, kbar: &Term, by: u32) -> Term {
        lam(
            &self.sig.lp,
            &self.sig.lw,
            self.pos(by),
            self.rho_case(0, var(0), by + 1, &kbar.shift_local(1)),
        )
    }

    fn rho_case(&self, s: usize, scrut: Term, by: u32, kbar: &Term) -> Term {
        if s + 1 == self.n() {
            return self.k_at(kbar, s, scrut, by);
        }
        let kbar1 = kbar.shift_local(1);
        Term::Case {
            lhs_level: self.sig.lp.clone(),
            rhs_level: self.sig.lp.clone(),
            motive_level: self.sig.lw.clone(),
            lhs: Rc::new(self.dom(s, by)),
            rhs: Rc::new(self.tail(s + 1, by)),
            motive: Rc::new(self.sig.w0(by + 1)),
            case_l: Rc::new(self.k_at(&kbar1, s, var(0), by + 1)),
            case_r: Rc::new(self.rho_case(s + 1, var(0), by + 1, &kbar1)),
            scrut: Rc::new(scrut),
        }
    }

    /// `CH(g)`'s factors: each child's own fact, `Π(y : A_t). El(ok(g(inj_t
    /// y)) c_t)` or `El(ok(g(inj_t ⟨⟩)) c_t)`.
    fn ch_items(&self, g: &Term, by: u32) -> Vec<(Type, Level)> {
        let lk = &self.sig.lk;
        (0..self.n())
            .map(|t| match &self.kids[t].dom {
                Some(_) => {
                    let at = app(g.shift_local(1), self.inj(t, var(0), by + 1));
                    let fact = self.sig.ok_ty(by + 1, &at, &self.idx(t, by));
                    (pi(&self.sig.lp, lk, self.dom(t, by), fact), join(&self.sig.lp, lk))
                }
                None => {
                    let unit = Term::Triv {
                        level: self.sig.lp.clone(),
                    };
                    let at = app(g.clone(), self.inj(t, unit, by));
                    (self.sig.ok_ty(by, &at, &self.idx(t, by)), lk.clone())
                }
            })
            .collect()
    }

    /// The `Σ` after the index equation, at the tree `sup(label; f)` (§3).
    fn rest_ty(&self, f: &Term, by: u32) -> (Type, Level) {
        let lf = self.lf();
        match self.n() {
            0 => (id_ty(&lf, self.kids_ty(by), self.f0(by), f.clone()), lf),
            1 => prod_ty(&self.ch_items(f, by)),
            _ => {
                let (kb, lkb) = prod_ty(&self.k_items(by));
                let ((q, lq), (ch, lch)) = self.after_kbar(f, by);
                let inner = join(&lq, &lch);
                let level = join(&lkb, &inner);
                (
                    Type::Sigma {
                        fst_level: lkb,
                        snd_level: inner,
                        fst: Rc::new(kb),
                        snd: Rc::new(Type::Sigma {
                            fst_level: lq,
                            snd_level: lch,
                            fst: Rc::new(q),
                            snd: Rc::new(ch),
                        }),
                    },
                    level,
                )
            }
        }
    }

    /// Under the `k̄` binder (`by + 1` past `B`): the children equation and
    /// `CH(f)`, the latter scoped one binder further, past `q`.
    fn after_kbar(&self, f: &Term, by: u32) -> ((Type, Level), (Type, Level)) {
        let lf = self.lf();
        let q = id_ty(&lf, self.kids_ty(by + 1), self.rho(&var(0), by + 1), f.shift_local(1));
        let ch = prod_ty(&self.ch_items(&f.shift_local(2), by + 2));
        ((q, lf), ch)
    }
}

fn code_or(t: &Type, what: &str, span: Span) -> R<Term> {
    match crate::code::code_of(t) {
        Some(c) => Ok(c),
        None => err(
            format!(
                "{what} has no code, which an indexed family with a recursive function \
                 field needs (docs/iwf-infinitary-design.md §1)"
            ),
            span,
        ),
    }
}

impl Br<'_> {
    /// `ok`'s branch (§5), at `B` = the branch past `f'`, `ih'`, `j`: the
    /// code of `Σ(e : Id(I; o; j)). REST`, its children's facts read through
    /// `ih'` rather than `ok`.
    fn ok_code(&self, f: &Term, ih: &Term, j: &Term, out: &Term, span: Span) -> R<Term> {
        let sig = &self.sig;
        let (lp, lk, lf) = (&sig.lp, &sig.lk, self.lf());
        let idx_eq = Term::TmId {
            level: sig.ilvl.clone(),
            ty: Rc::new(code_or(&sig.ity, "the index type", span)?),
            lhs: Rc::new(out.clone()),
            rhs: Rc::new(j.clone()),
        };
        let facts = |by: u32, ihv: &Term| -> R<Vec<(Term, Level)>> {
            (0..self.n())
                .map(|t| {
                    Ok(match &self.kids[t].dom {
                        Some(_) => (
                            Term::TmPi {
                                dom_level: lp.clone(),
                                cod_level: lk.clone(),
                                dom: Rc::new(code_or(&self.dom(t, by), "a recursive function field's domain", span)?),
                                cod: Rc::new(app(
                                    app(ihv.shift_local(1), self.inj(t, var(0), by + 1)),
                                    self.idx(t, by),
                                )),
                            },
                            join(lp, lk),
                        ),
                        None => {
                            let unit = Term::Triv { level: lp.clone() };
                            (app(app(ihv.clone(), self.inj(t, unit, by)), self.idx(t, by)), lk.clone())
                        }
                    })
                })
                .collect()
        };
        let (rest, lrest) = match self.n() {
            0 => (
                Term::TmId {
                    level: lf.clone(),
                    ty: Rc::new(code_or(&self.kids_ty(0), "the children's type", span)?),
                    lhs: Rc::new(self.f0(0)),
                    rhs: Rc::new(f.clone()),
                },
                lf.clone(),
            ),
            1 => facts(0, ih)?.pop().expect("one fact"),
            _ => {
                let kcodes = self
                    .k_items(0)
                    .iter()
                    .map(|(t, l)| Ok((code_or(t, "the children's type", span)?, l.clone())))
                    .collect::<R<Vec<_>>>()?;
                let (kb, lkb) = prod_code(&kcodes);
                let q = Term::TmId {
                    level: lf.clone(),
                    ty: Rc::new(code_or(&self.kids_ty(1), "the children's type", span)?),
                    lhs: Rc::new(self.rho(&var(0), 1)),
                    rhs: Rc::new(f.shift_local(1)),
                };
                let (ch, lch) = prod_code(&facts(2, &ih.shift_local(2))?);
                let inner = join(&lf, &lch);
                (
                    Term::TmSigma {
                        fst_level: lkb.clone(),
                        snd_level: inner.clone(),
                        fst: Rc::new(kb),
                        snd: Rc::new(Term::TmSigma {
                            fst_level: lf.clone(),
                            snd_level: lch,
                            fst: Rc::new(q),
                            snd: Rc::new(ch),
                        }),
                    },
                    join(&lkb, &inner),
                )
            }
        };
        Ok(Term::TmSigma {
            fst_level: sig.ilvl.clone(),
            snd_level: lrest,
            fst: Rc::new(idx_eq),
            snd: Rc::new(rest.shift_local(1)),
        })
    }
}

impl Elaborator {
    /// Constructor `k`'s written result index and recursive fields,
    /// elaborated in `acx` (the stored fields aliased there), with the index
    /// type `ity` scoped in `acx`.
    ///
    /// The function domains are elaborated from their spelling while the
    /// signature is built, where `acx` binds the type parameters; once it
    /// exists, `pos` (`P` at this branch's label, at `lp`) is split into them
    /// instead, since a family read back from its type has no arguments to
    /// bind a parameter to.
    #[allow(clippy::too_many_arguments)]
    fn iw_branch(
        &self,
        acx: &Cx,
        ind: &Inductive,
        k: usize,
        ity: &Type,
        ilvl: &Level,
        pos: Option<(&Type, &Level)>,
        span: Span,
    ) -> R<(Term, Vec<Kid>)> {
        let ctor = &ind.ctors[k];
        let _scope = self.use_inductive_scope(ind);
        let out = self.elab_check(acx, res_expr(ind, k), ity, ilvl)?;
        let n = ctor.kind.iter().filter(|c| matches!(c, FieldKind::Plain | FieldKind::FnChild)).count();
        let mut doms = match pos {
            Some((p, _)) => self.split_positions(acx, p, n, span)?.into_iter(),
            None => Vec::new().into_iter(),
        };
        let mut kids = Vec::new();
        for (j, kind) in ctor.kind.iter().enumerate() {
            match kind {
                FieldKind::Plain => {
                    doms.next();
                    let idx = self.elab_check(acx, child_index(ctor, j), ity, ilvl)?;
                    kids.push(Kid { field: j, dom: None, idx });
                }
                FieldKind::FnChild => {
                    let TyKind::Fn { binder, dom, .. } = &ctor.fields[j].1.kind else {
                        return err("internal: a recursive function field is not a `->`", span);
                    };
                    let (a, la) = match (doms.next(), pos) {
                        (Some(a), Some((_, lp))) => (a, lp.clone()),
                        _ => self.elab_ty(acx, dom)?,
                    };
                    let mut ycx = acx.clone();
                    ycx.push(binder.clone().unwrap_or_else(|| "#y".into()), a.clone(), la.clone());
                    let idx = self.elab_check(&ycx, child_index(ctor, j), &ity.shift_local(1), ilvl)?;
                    kids.push(Kid { field: j, dom: Some((a, la)), idx });
                }
                _ => {}
            }
        }
        Ok((out, kids))
    }

    /// `P(label)` read back into its `n` factors: the type itself for one
    /// recursive field, the right-nested sum's summands for more (§4).
    fn split_positions(&self, cx: &Cx, pos: &Type, n: usize, span: Span) -> R<Vec<Type>> {
        let mut out = Vec::with_capacity(n);
        let mut rest = pos.clone();
        for _ in 1..n {
            match self.whnf(cx, &rest, span)? {
                Type::Sum { lhs, rhs, .. } => {
                    out.push(self.whnf(cx, &lhs, span)?);
                    rest = (*rhs).clone();
                }
                _ => return err("internal: a branch's positions are not a sum of its fields' domains", span),
            }
        }
        if n > 0 {
            out.push(self.whnf(cx, &rest, span)?);
        }
        Ok(out)
    }

    // -- the type (§4, §5) ----------------------------------------------------

    /// The `W`-encoded signature at type arguments `args`, scoped in `cx`.
    pub(crate) fn iw_sig(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        span: Span,
    ) -> R<Rc<IwSig>> {
        let shape_decl = ind
            .skel
            .as_ref()
            .expect("an IWf-route declaration has a shape declaration");
        let n = ind.ctors.len();
        let (shape, ls) = self.lower_instance(cx, shape_decl, args, &[], span)?;
        let (ity, ilvl) = self.index_type_of(cx, ind, span)?;
        let spine = self.spine(&shape, &ls, n, span)?;
        // The function domains are spelled over the type parameters: bound
        // here, to `args`, for every branch below.
        let mut cx = cx.clone();
        let tyvars = self.field_scope_cx(&cx, ind, args, &[]).tyvars;
        cx.tyvars.extend(tyvars);
        let cx = &cx;
        // The function domains' one level `lp` (§1.3), read at a generic
        // payload, where the written indices are checked too.
        let mut lp: Option<(Level, String)> = None;
        for k in 0..n {
            let mut pcx = cx.clone();
            pcx.push("#p".into(), (*spine.ctors[k].0).clone(), spine.ctors[k].1.clone());
            let dcx = self.decl_payload_cx(&pcx, ind, &spine, k, &Rc::new(var(0)), 1, span)?;
            let (_, kids) = self.iw_branch(&dcx, ind, k, &ity.shift_local(1), &ilvl, None, span)?;
            for kid in &kids {
                let Some((a, la)) = &kid.dom else { continue };
                code_or(a, &format!("the domain of `{}`'s recursive function field", ind.ctors[k].name), span)?;
                match &lp {
                    Some((l, first)) if !l.equiv(la) => {
                        return err(
                            format!(
                                "the recursive function fields of `{first}` and `{}` have \
                                 domains at different universe levels; an indexed family \
                                 with function fields needs one level for all of them \
                                 (docs/iwf-infinitary-design.md §1)",
                                ind.ctors[k].name
                            ),
                            span,
                        );
                    }
                    Some(_) => {}
                    None => lp = Some((la.clone(), ind.ctors[k].name.clone())),
                }
            }
        }
        let Some((lp, _)) = lp else {
            return err("internal: an infinitary IWf-route family has no function field", span);
        };
        let lw = join(&ls, &lp);
        let lk = join(&ilvl, &lw);
        // P over (Γ, x : S): a case tree into codes at `Ty lp`.
        let mut xcx = cx.clone();
        xcx.push("#x".into(), shape.clone(), ls.clone());
        let pos_body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _: &Type| -> R<Term> {
            let dcx = self.decl_payload_cx(bcx, ind, &spine, k, value, d, span)?;
            let (_, kids) = self.iw_branch(&dcx, ind, k, &ity.shift_local(d), &ilvl, None, span)?;
            let mut codes = kids
                .iter()
                .map(|kid| match &kid.dom {
                    Some((a, _)) => code_or(a, "a recursive function field's domain", span),
                    None => Ok(Term::TmUnit { level: lp.clone() }),
                })
                .collect::<R<Vec<_>>>()?;
            let Some(mut acc) = codes.pop() else {
                return Ok(Term::TmEmpty { level: lp.clone() });
            };
            while let Some(c) = codes.pop() {
                acc = Term::TmSum {
                    lhs_level: lp.clone(),
                    rhs_level: lp.clone(),
                    lhs: Rc::new(c),
                    rhs: Rc::new(acc),
                };
            }
            Ok(acc)
        };
        let ptree = self.idx_case_tree(
            &xcx,
            &spine,
            n,
            0,
            Type::Ty(lp.clone()),
            &Level::succ(lp.clone()),
            Rc::new(var(0)),
            1,
            &pos_body,
        )?;
        let pos = Type::El {
            level: lp.clone(),
            tm: Rc::new(ptree),
        };
        let mut sig = IwSig {
            ls: ls.clone(),
            lp: lp.clone(),
            lw: lw.clone(),
            lk: lk.clone(),
            ilvl: ilvl.clone(),
            ity: Rc::new(ity.clone()),
            shape: Rc::new(shape.clone()),
            pos: Rc::new(pos),
            // Not read until `ok` exists: nothing below asks for it.
            ok: Rc::new(Term::Zero),
        };
        code_or(&sig.w0(0), &format!("a field type of `{}`", ind.name), span)?;
        // ok over (Γ, t): elim_W at the motive `Π(j : I). Ty lk`, its step a
        // convoy case tree on the shape (tier 2 §5's, with the index).
        let lf = sig.lf();
        let ty_lk = Type::Ty(lk.clone());
        let succ_lk = Level::succ(lk.clone());
        let jpi_lvl = join(&ilvl, &succ_lk);
        // `Π(j : I). Ty lk`, `by` binders past Γ.
        let jpi = |by: u32| pi(&ilvl, &succ_lk, ity.shift_local(by), ty_lk.clone());
        // `Π(p : P v). Π(j : I). Ty lk`, the predicate's ih.
        let ih_ty = |by: u32, v: &Term| pi(&lp, &jpi_lvl, sig.pos_at(by, v), jpi(by + 1));
        let lih = join(&lp, &jpi_lvl);
        let qin = join(&lih, &jpi_lvl);
        let lq = join(&lf, &qin);
        // Q(v) = Π(f' : Π(p : P v). W₀). Π(ih' : …). Π(j : I). Ty lk
        let q = |by: u32, v: &Term| {
            pi(
                &lf,
                &qin,
                sig.kids_ty(by, v),
                pi(&lih, &jpi_lvl, ih_ty(by + 1, &v.shift_local(1)), jpi(by + 2)),
            )
        };
        let mut c3 = cx.clone();
        c3.push("#a".into(), shape.clone(), ls.clone());
        c3.push("#f".into(), sig.kids_ty(1, &var(0)), lf.clone());
        c3.push("#ih".into(), ih_ty(2, &var(1)), lih.clone());
        let ok_body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _: &Type| -> R<Term> {
            let lab = inject(&spine, k, n, (**value).clone(), d);
            let mut ccx = bcx.clone();
            ccx.push("#f".into(), sig.kids_ty(d, &lab), lf.clone());
            ccx.push("#ih".into(), ih_ty(d + 1, &lab.shift_local(1)), lih.clone());
            ccx.push("#j".into(), ity.shift_local(d + 2), ilvl.clone());
            let dd = d + 3;
            let dcx = self.decl_payload_cx(&ccx, ind, &spine, k, &Rc::new(value.shift_local(3)), dd, span)?;
            let (out, kids) = self.iw_branch(&dcx, ind, k, &ity.shift_local(dd), &ilvl, None, span)?;
            let br = Br {
                sig: sig.shift_local(dd),
                kids: &kids,
                lab: lab.shift_local(3),
            };
            let code = br.ok_code(&var(2), &var(1), &var(0), &out, span)?;
            Ok(lam(
                &lf,
                &qin,
                sig.kids_ty(d, &lab),
                lam(
                    &lih,
                    &jpi_lvl,
                    ih_ty(d + 1, &lab.shift_local(1)),
                    lam(&ilvl, &succ_lk, ity.shift_local(d + 2), code),
                ),
            ))
        };
        let tree = self.idx_case_tree(&c3, &spine, n, 0, q(4, &var(0)), &lq, Rc::new(var(2)), 3, &ok_body)?;
        // The step over (Γ, a, f, ih), moved under the tree `t` the predicate
        // is a function of.
        let step = app(app(tree, var(1)), var(0)).shift_local_above(1, 3);
        sig.ok = Rc::new(Term::ElimW {
            shape_level: ls.clone(),
            pos_level: lp.clone(),
            motive_level: jpi_lvl.clone(),
            shape: Rc::new(shape.shift_local(1)),
            pos: Rc::new(sig.pos.shift_local_above(1, 1)),
            motive: Rc::new(jpi(2)),
            step: Rc::new(step),
            scrut: Rc::new(var(0)),
        });
        Ok(Rc::new(sig))
    }

    // -- constructors (§6) ----------------------------------------------------

    /// `⟦C_k(b̄, r̄)⟧ = ⟨sup(ℓ; kids), ⟨refl(o), REST⟩⟩` at `D(m)`. `acx` is
    /// the `IWf` route's context binding the stored fields to the written
    /// arguments, `target` the written result index there, already checked
    /// against `m`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_iw_ctor(
        &self,
        cx: &Cx,
        acx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[&heather_syntax::ast::Expr],
        sig: &IwSig,
        label: Term,
        target: &Term,
        m: &Term,
        span: Span,
    ) -> R<Term> {
        let pos = sig.pos_at(0, &label);
        let (_, kids) = self.iw_branch(acx, ind, i, &sig.ity, &sig.ilvl, Some((&pos, &sig.lp)), span)?;
        let br = Br {
            sig: sig.clone(),
            kids: &kids,
            lab: label.clone(),
        };
        let (lp, lw, lk, lf) = (&sig.lp, &sig.lw, &sig.lk, sig.lf());
        let fl = sig.lvl();
        // Each child at the family instance its written index names.
        let mut rs: Vec<Term> = Vec::new();
        for (t, kid) in kids.iter().enumerate() {
            let arg = args[kid.field];
            let r = match &kid.dom {
                None => self.elab_check(cx, arg, &sig.fam(0, &br.idx(t, 0)), &fl)?,
                Some((a, _)) => {
                    let ty = pi(lp, &fl, a.clone(), sig.fam(1, &br.idx(t, 0)));
                    self.elab_check(cx, arg, &ty, &join(lp, &fl))?
                }
            };
            rs.push(r);
        }
        // `r_t y` (or `r_t`), `by` binders past Γ.
        let r_at = |t: usize, y: Term, by: u32| -> Term {
            let r = rs[t].shift_local(by);
            match &kids[t].dom {
                None => r,
                Some(_) => Term::App {
                    fun: Rc::new(r),
                    dom_level: lp.clone(),
                    cod_level: fl.clone(),
                    dom: Rc::new(br.dom(t, by)),
                    cod: Rc::new(sig.fam(by + 1, &br.idx(t, by))),
                    arg: Rc::new(y),
                },
            }
        };
        // The index `r_t y` is at.
        let idx_at = |t: usize, y: &Term, by: u32| -> Term {
            match &kids[t].dom {
                None => br.idx(t, by),
                Some(_) => br.idx(t, by).inst_top(0, y),
            }
        };
        let tree_at = |t: usize, y: Term, by: u32| sig.fst(by, &idx_at(t, &y, by), r_at(t, y, by));
        let proof_at = |t: usize, y: Term, by: u32| sig.snd(by, &idx_at(t, &y, by), r_at(t, y, by));
        let unit = || Term::Triv { level: lp.clone() };
        let n = kids.len();
        let (kids_tm, rest) = match n {
            0 => {
                let f0 = br.f0(0);
                (f0.clone(), refl(&lf, br.kids_ty(0), f0))
            }
            1 => {
                let kids_tm = lam(lp, lw, br.pos(0), tree_at(0, var(0), 1));
                let pr = match &kids[0].dom {
                    None => proof_at(0, unit(), 0),
                    Some(_) => lam(lp, lk, br.dom(0, 0), proof_at(0, var(0), 1)),
                };
                (kids_tm, pr)
            }
            _ => {
                // The stored children k̄, the tree's children as ρ(k̄), and
                // each child's own fact.
                let k_items = br.k_items(0);
                let ks: Vec<Term> = (0..n)
                    .map(|t| match &kids[t].dom {
                        None => tree_at(t, unit(), 0),
                        Some(_) => lam(lp, lw, br.dom(t, 0), tree_at(t, var(0), 1)),
                    })
                    .collect();
                let kbar = tuple(&k_items, ks);
                let kids_tm = br.rho(&kbar, 0);
                let ch_items = br.ch_items(&kids_tm, 0);
                let prs: Vec<Term> = (0..n)
                    .map(|t| match &kids[t].dom {
                        None => proof_at(t, unit(), 0),
                        Some(_) => lam(lp, lk, br.dom(t, 0), proof_at(t, var(0), 1)),
                    })
                    .collect();
                let cs = tuple(&ch_items, prs);
                let q = refl(&lf, br.kids_ty(0), kids_tm.clone());
                let (kb, lkb) = prod_ty(&k_items);
                let ((qty, lq), (chty, lch)) = br.after_kbar(&kids_tm, 0);
                let inner_ty = Type::Sigma {
                    fst_level: lq.clone(),
                    snd_level: lch.clone(),
                    fst: Rc::new(qty.clone()),
                    snd: Rc::new(chty.clone()),
                };
                let inner_lvl = join(&lq, &lch);
                let inner = Term::Pair {
                    fst_level: lq,
                    snd_level: lch,
                    fst_ty: Rc::new(qty.inst_top(0, &kbar)),
                    snd_ty: Rc::new(chty.inst_top_above(0, 1, &kbar)),
                    fst: Rc::new(q),
                    snd: Rc::new(cs),
                };
                let rest = Term::Pair {
                    fst_level: lkb,
                    snd_level: inner_lvl,
                    fst_ty: Rc::new(kb),
                    snd_ty: Rc::new(inner_ty),
                    fst: Rc::new(kbar),
                    snd: Rc::new(inner),
                };
                (kids_tm, rest)
            }
        };
        let (rty, lr) = br.rest_ty(&kids_tm, 0);
        let proof = pair(
            (&id_ty(&sig.ilvl, (*sig.ity).clone(), target.clone(), m.clone()), &sig.ilvl),
            (&rty, &lr),
            refl(&sig.ilvl, (*sig.ity).clone(), target.clone()),
            rest,
        );
        Ok(sig.pair(0, m, sig.sup(0, label, kids_tm), proof))
    }

    // -- match (§7, §8) -------------------------------------------------------

    /// `match s = elim_W(x:S. P; w. M'(w); a f ih. STEP; fst s) m (snd s)`,
    /// with `M'(w) = Π(j : I). Π(c : El(ok w j)). M(j, ⟨w, c⟩)`. The `IWf`
    /// route has already ordered the arms and built the motive over
    /// `(Γ, j, z)` (`env.motive`).
    pub(crate) fn iw_match(&self, cx: &Cx, env: &ArmEnv, sig: &IwSig, scrut: Term) -> R<Term> {
        let ind = env.ind;
        let n = ind.ctors.len();
        let m = Rc::clone(&env.fam.idx);
        let mlvl = env.mlvl;
        let w = MatchLevels::new(sig, mlvl);
        let mut c3 = cx.clone();
        c3.push("#a".into(), (*sig.shape).clone(), sig.ls.clone());
        c3.push("#f".into(), sig.kids_ty(1, &var(0)), sig.lf());
        c3.push("#ih".into(), w.ih_ty(env, sig, 0, 2, &var(1), &var(0)), w.lih.clone());
        let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _: &Type| -> R<Term> {
            self.iw_arm(bcx, env, sig, &w, k, value, d)
        };
        let tree = self.idx_case_tree(
            &c3,
            env.spine,
            n,
            0,
            w.q(env, sig, 0, 4, &var(0)),
            &w.lq,
            Rc::new(var(2)),
            3,
            &body,
        )?;
        let step = app(app(tree, var(1)), var(0));
        let elim = Term::ElimW {
            shape_level: sig.ls.clone(),
            pos_level: sig.lp.clone(),
            motive_level: w.lmp.clone(),
            shape: Rc::clone(&sig.shape),
            pos: Rc::clone(&sig.pos),
            motive: Rc::new(w.m_prime(env, sig, 0, 1, &var(0))),
            step: Rc::new(step),
            scrut: Rc::new(sig.fst(0, &m, scrut.clone())),
        };
        Ok(app(app(elim, (*m).clone()), sig.snd(0, &m, scrut)))
    }

    /// One branch of the step: `λf'. λih'. λj. λc. J(I; o; …; B₁; j; fst c)
    /// (snd c)` (§7), the user's arm inside `B₁`.
    #[allow(clippy::too_many_arguments)]
    fn iw_arm(
        &self,
        bcx: &Cx,
        env: &ArmEnv,
        sig: &IwSig,
        w: &MatchLevels,
        k: usize,
        value: &Rc<Term>,
        d: u32,
    ) -> R<Term> {
        let ind = env.ind;
        let ctor = &ind.ctors[k];
        let span = env.ordered[k].map_or(env.span, |a| a.span);
        let n_all = ind.ctors.len();
        let mlvl = env.mlvl;
        let (lk, li, lf) = (&sig.lk, &sig.ilvl, sig.lf());
        let lab = inject(env.spine, k, n_all, (**value).clone(), d);
        let mut ccx = bcx.clone();
        ccx.push("#f".into(), sig.kids_ty(d, &lab), lf.clone());
        ccx.push("#ih".into(), w.ih_ty(env, sig, 0, d + 1, &lab.shift_local(1), &var(0)), w.lih.clone());
        ccx.push("#j".into(), sig.ity.shift_local(d + 2), li.clone());
        let sup3 = sig.sup(d + 3, lab.shift_local(3), var(2));
        ccx.push("#c".into(), sig.ok_ty(d + 3, &sup3, &var(0)), lk.clone());
        // In BODY: f' = 3, ih' = 2, j = 1, c = 0.
        let dd = d + 4;
        let dcx = self.decl_payload_cx(&ccx, ind, env.spine, k, &Rc::new(value.shift_local(4)), dd, span)?;
        let pos = sig.pos_at(dd, &lab.shift_local(4));
        let (out, kids) = self.iw_branch(&dcx, ind, k, &sig.ity.shift_local(dd), li, Some((&pos, &sig.lp)), span)?;
        let sigd = sig.shift_local(dd);
        let br = Br {
            sig: sigd.clone(),
            kids: &kids,
            lab: lab.shift_local(4),
        };
        let n = kids.len();
        let value_b = value.shift_local(4);
        let ity_at = |by: u32| sigd.ity.shift_local(by);
        let out_at = |by: u32| out.shift_local(by);
        let mot = |m: Term, z: Term, by: u32| env.mot_at(m, z, dd + by);
        // `⟨sup(label; g), ⟨e, r⟩⟩ : D(j)`, `by` past B.
        // The pair's second type is under `e`'s binder, so `f` is weakened
        // past it: a motive that ignores `z` never checks this annotation,
        // one that reads it does.
        let value_at = |by: u32, j: Term, g: Term, e: Term, r: Term, f_for_rest: &Term| -> Term {
            let (rty, lr) = br.rest_ty(&f_for_rest.shift_local(1), by + 1);
            let inner = Term::Pair {
                fst_level: li.clone(),
                snd_level: lr,
                fst_ty: Rc::new(id_ty(li, ity_at(by), out_at(by), j.clone())),
                snd_ty: Rc::new(rty),
                fst: Rc::new(e),
                snd: Rc::new(r),
            };
            sigd.pair(by, &j, sigd.sup(by, br.lab(by), g), inner)
        };
        let (r0, lr) = br.rest_ty(&var(3), 0);
        // J₁'s motive over (B, j', e'): Π(r : R(f')). M(j', ⟨sup(v; f'), ⟨e', r⟩⟩).
        let motive1 = pi(
            &lr,
            mlvl,
            br.rest_ty(&var(5), 2).0,
            mot(var(2), value_at(3, var(2), var(6), var(1), var(0), &var(6)), 3),
        );
        // B₁, at (B, r): r = 0, c = 1, j = 2, ih' = 3, f' = 4.
        let goal1 = mot(
            out_at(1),
            value_at(1, out_at(1), var(4), refl(li, ity_at(1), out_at(1)), var(0), &var(4)),
            1,
        );
        let mut rcx = ccx.clone();
        rcx.push("#r".into(), r0.clone(), lr.clone());
        let impossible = env.inverted
            && !env.motive_unit
            && matches!(self.whnf(&rcx, &goal1, span)?, Type::Unit { .. });
        let b1_body = if impossible {
            let Type::Unit { level } = self.whnf(&rcx, &goal1, span)? else {
                unreachable!("checked just above")
            };
            Term::Triv { level }
        } else {
            let Some(arm) = env.ordered[k] else {
                return err(format!("`{}` is missing an arm for `{}`", env.keyword, ctor.name), span);
            };
            let names: Vec<Option<String>> = arm.binders.iter().map(|b| Some(b.name().to_string())).collect();
            match n {
                // One recursive field: no children equation (§3).
                1 => {
                    let acx = self.iw_arm_cx(&rcx, env, &br, k, &value_b, &names, 1, &ArmKids::One { f: var(4), ih: var(3), cs: var(0) }, span)?;
                    self.iw_arm_body(&acx, env, arm, &goal1)?
                }
                // A leaf: transport along `Id(f₀; f')` from `f₀`.
                0 => {
                    let acx = self.iw_arm_cx(&rcx, env, &br, k, &value_b, &names, 1, &ArmKids::One { f: var(4), ih: var(3), cs: var(0) }, span)?;
                    let f0 = br.f0(1);
                    let goal = mot(
                        out_at(1),
                        value_at(1, out_at(1), f0.clone(), refl(li, ity_at(1), out_at(1)), refl(&lf, br.kids_ty(1), f0.clone()), &f0),
                        1,
                    );
                    let arm_tm = self.iw_arm_body(&acx, env, arm, &goal)?;
                    let motive = mot(
                        out_at(3),
                        value_at(3, out_at(3), var(1), refl(li, ity_at(3), out_at(3)), var(0), &var(1)),
                        3,
                    );
                    Term::J {
                        ty_level: lf.clone(),
                        motive_level: mlvl.clone(),
                        ty: Rc::new(br.kids_ty(1)),
                        lhs: Rc::new(f0),
                        motive: Rc::new(motive),
                        case: Rc::new(arm_tm),
                        rhs: Rc::new(var(4)),
                        proof: Rc::new(var(0)),
                    }
                }
                // Two or more: transport along `Id(ρ(k̄); f')` from `ρ(k̄)`,
                // with `CH` and the ih generalized along (§7).
                _ => {
                    let (kb, lkb) = prod_ty(&br.k_items(1));
                    // r = ⟨k̄, ⟨q, cs⟩⟩, at (B, r).
                    let ((qty, lq), (chty, lch)) = br.after_kbar(&var(4), 1);
                    let inner_ty = Type::Sigma {
                        fst_level: lq.clone(),
                        snd_level: lch.clone(),
                        fst: Rc::new(qty.clone()),
                        snd: Rc::new(chty.clone()),
                    };
                    let inner_lvl = join(&lq, &lch);
                    let kbar = Term::Fst {
                        fst_level: lkb.clone(),
                        snd_level: inner_lvl.clone(),
                        fst_ty: Rc::new(kb.clone()),
                        snd_ty: Rc::new(inner_ty.clone()),
                        pair: Rc::new(var(0)),
                    };
                    let rest_of_r = Term::Snd {
                        fst_level: lkb.clone(),
                        snd_level: inner_lvl.clone(),
                        fst_ty: Rc::new(kb.clone()),
                        snd_ty: Rc::new(inner_ty.clone()),
                        pair: Rc::new(var(0)),
                    };
                    let q_here = qty.inst_top(0, &kbar);
                    let ch_here = chty.inst_top_above(0, 1, &kbar);
                    let q_of = Term::Fst {
                        fst_level: lq.clone(),
                        snd_level: lch.clone(),
                        fst_ty: Rc::new(q_here.clone()),
                        snd_ty: Rc::new(ch_here.clone()),
                        pair: Rc::new(rest_of_r.clone()),
                    };
                    let cs_of = Term::Snd {
                        fst_level: lq.clone(),
                        snd_level: lch.clone(),
                        fst_ty: Rc::new(q_here),
                        snd_ty: Rc::new(ch_here),
                        pair: Rc::new(rest_of_r),
                    };
                    // The motive's value at (g, q, cs), `by` past B; k̄ is
                    // `kbar` shifted from (B, r).
                    let z_at = |by: u32, g: Term, q: Term, cs: Term| -> Term {
                        let kb_by = kbar.shift_local(by - 1);
                        let ((qt, lq2), (ct, lc2)) = br.after_kbar(&g, by);
                        let inner = Term::Pair {
                            fst_level: lq2.clone(),
                            snd_level: lc2.clone(),
                            fst_ty: Rc::new(qt.inst_top(0, &kb_by)),
                            snd_ty: Rc::new(ct.inst_top_above(0, 1, &kb_by)),
                            fst: Rc::new(q),
                            snd: Rc::new(cs),
                        };
                        let (kb2, lkb2) = prod_ty(&br.k_items(by));
                        let mid = Term::Pair {
                            fst_level: lkb2,
                            snd_level: join(&lq2, &lc2),
                            fst_ty: Rc::new(kb2),
                            snd_ty: Rc::new(Type::Sigma {
                                fst_level: lq2,
                                snd_level: lc2,
                                fst: Rc::new(qt),
                                snd: Rc::new(ct),
                            }),
                            fst: Rc::new(kb_by),
                            snd: Rc::new(inner),
                        };
                        value_at(by, out_at(by), g.clone(), refl(li, ity_at(by), out_at(by)), mid, &g)
                    };
                    // J₂'s motive over (B, r, g, q): Π(cs : CH(g)). Π(ih'' : Π(p : P v). M'(g p)). M(o, z),
                    // the body at (B, r, g, q, cs, ih''): g = 3, q = 2, cs = 1.
                    let (ch_g, lch_g) = prod_ty(&br.ch_items(&var(1), 3));
                    let ih_g = w.ih_ty(env, &sigd, dd, 4, &br.lab(4), &var(2));
                    let motive2 = pi(
                        &lch_g,
                        &join(&w.lih, mlvl),
                        ch_g,
                        pi(&w.lih, mlvl, ih_g, mot(out_at(5), z_at(5, var(3), var(2), var(1)), 5)),
                    );
                    // The base case at g := ρ(k̄), q := refl: λcs. λih''. ARM.
                    let rho1 = br.rho(&kbar, 1);
                    let (ch_b, lch_b) = prod_ty(&br.ch_items(&rho1, 1));
                    let ih_b = w.ih_ty(env, &sigd, dd, 2, &br.lab(2), &rho1.shift_local(1));
                    let mut acx0 = rcx.clone();
                    acx0.push("#cs".into(), ch_b.clone(), lch_b.clone());
                    acx0.push("#ih".into(), ih_b.clone(), w.lih.clone());
                    let kids_arm = ArmKids::Many { kbar: kbar.shift_local(2), ih: var(0), cs: var(1) };
                    let acx = self.iw_arm_cx(&acx0, env, &br, k, &value_b, &names, 3, &kids_arm, span)?;
                    let rho3 = rho1.shift_local(2);
                    let goal = mot(out_at(3), z_at(3, rho3.clone(), refl(&lf, br.kids_ty(3), rho3), var(1)), 3);
                    let arm_tm = self.iw_arm_body(&acx, env, arm, &goal)?;
                    let case = lam(&lch_b, &join(&w.lih, mlvl), ch_b, lam(&w.lih, mlvl, ih_b, arm_tm));
                    let j2 = Term::J {
                        ty_level: lf.clone(),
                        motive_level: join(&lch_g, &join(&w.lih, mlvl)),
                        ty: Rc::new(br.kids_ty(1)),
                        lhs: Rc::new(rho1),
                        motive: Rc::new(motive2),
                        case: Rc::new(case),
                        rhs: Rc::new(var(4)),
                        proof: Rc::new(q_of),
                    };
                    app(app(j2, cs_of), var(3))
                }
            }
        };
        let b1 = lam(&lr, mlvl, r0.clone(), b1_body);
        let c_fst = Term::Fst {
            fst_level: li.clone(),
            snd_level: lr.clone(),
            fst_ty: Rc::new(id_ty(li, ity_at(0), out.clone(), var(1))),
            snd_ty: Rc::new(br.rest_ty(&var(4), 1).0),
            pair: Rc::new(var(0)),
        };
        let c_snd = Term::Snd {
            fst_level: li.clone(),
            snd_level: lr.clone(),
            fst_ty: Rc::new(id_ty(li, ity_at(0), out.clone(), var(1))),
            snd_ty: Rc::new(br.rest_ty(&var(4), 1).0),
            pair: Rc::new(var(0)),
        };
        let j1 = Term::J {
            ty_level: li.clone(),
            motive_level: join(&lr, mlvl),
            ty: Rc::new(ity_at(0)),
            lhs: Rc::new(out.clone()),
            motive: Rc::new(motive1),
            case: Rc::new(b1),
            rhs: Rc::new(var(1)),
            proof: Rc::new(c_fst),
        };
        let body = app(j1, c_snd);
        // λf'. λih'. λj. λc. BODY
        let c_ty = sig.ok_ty(d + 3, &sup3, &var(0));
        Ok(lam(
            &lf,
            &w.qin,
            sig.kids_ty(d, &lab),
            lam(
                &w.lih,
                &w.lmp,
                w.ih_ty(env, sig, 0, d + 1, &lab.shift_local(1), &var(0)),
                lam(
                    li,
                    &join(lk, mlvl),
                    sig.ity.shift_local(d + 2),
                    lam(lk, mlvl, c_ty, body),
                ),
            ),
        ))
    }

    /// The arm's goal, decoded where the motive inverted the index (the
    /// `IWf` route's display rule), and the arm checked against it.
    fn iw_arm_body(&self, acx: &Cx, env: &ArmEnv, arm: &heather_syntax::ast::Arm, goal: &Type) -> R<Term> {
        let goal = if env.inverted {
            let g = self.whnf(acx, goal, arm.span)?;
            crate::inductive::decode_deep(&g).unwrap_or(g)
        } else {
            goal.clone()
        };
        self.elab_check(acx, &arm.body, &goal, env.mlvl)
    }

    /// The arm's context: each payload field aliased to its projection, each
    /// recursive field to its rebuilt child (§7's table), and the recursion
    /// guard over them. `cx` is `by` binders past `B`, and `value` is the
    /// branch's payload value scoped at `B`.
    #[allow(clippy::too_many_arguments)]
    fn iw_arm_cx(
        &self,
        cx: &Cx,
        env: &ArmEnv,
        br: &Br,
        k: usize,
        value: &Term,
        names: &[Option<String>],
        by: u32,
        kids_in: &ArmKids,
        span: Span,
    ) -> R<Cx> {
        let ind = env.ind;
        let sigd = &br.sig;
        let lp = &sigd.lp;
        let fl = sigd.lvl();
        let mlvl = env.mlvl;
        let mut acx = cx.clone();
        let past = (cx.names.len() - env.gamma0.len()) as u32;
        self.payload_aliases(&mut acx, ind, env.spine, k, &Rc::new(value.shift_local(by)), past, names, span)?;
        let depth = acx.names.len();
        let mut children = Vec::new();
        let mut fn_children = Vec::new();
        let mut rebind = Vec::new();
        for t in 0..br.n() {
            let kid = &br.kids[t];
            let name = names[kid.field].clone().unwrap_or_else(|| "_".into());
            let c = br.idx(t, by);
            let (term, ty, level) = match &kid.dom {
                None => {
                    let unit = Term::Triv { level: lp.clone() };
                    let (tree, fact, ihp) = arm_piece(br, kids_in, t, unit, 0, by);
                    let term = sigd.pair(by, &c, tree, fact.clone());
                    let ih = app(app(ihp, c.clone()), fact);
                    let ih_ty = env.mot_at(c.clone(), term.clone(), past);
                    children.push((Rc::new(term.clone()), Rc::new(ih), ih_ty, mlvl.clone()));
                    // Under a member constructor the varying index is the
                    // member's own, the constructor's one argument
                    // (docs/mutual-inductive-design.md §5).
                    let at = if env.rebind_inner {
                        ind.index_ty
                            .as_ref()
                            .and_then(|ity| self.index_head(&acx, ity, &c, span))
                            .and_then(|(_, args)| args.first().map(|a| (**a).clone()))
                            .unwrap_or_else(|| c.clone())
                    } else {
                        c.clone()
                    };
                    rebind.push(Rc::new(at));
                    (term, sigd.fam(by, &c), fl.clone())
                }
                Some(_) => {
                    let a = br.dom(t, by);
                    let (tree, fact, ihp) = arm_piece(br, kids_in, t, var(0), 1, by);
                    let k_term = lam(lp, &fl, a.clone(), sigd.pair(by + 1, &c, tree, fact.clone()));
                    let ih = lam(lp, mlvl, a.clone(), app(app(ihp, c.clone()), fact));
                    let at_y = Term::App {
                        fun: Rc::new(k_term.shift_local(1)),
                        dom_level: lp.clone(),
                        cod_level: fl.clone(),
                        dom: Rc::new(a.shift_local(1)),
                        cod: Rc::new(sigd.fam(by + 2, &c.shift_local_above(1, 1))),
                        arg: Rc::new(var(0)),
                    };
                    let ih_ty = pi(lp, mlvl, a.clone(), env.mot_at(c.clone(), at_y, past + 1));
                    // Under a member constructor, the member's own index,
                    // read under `y` as the plain case reads it.
                    let rebind = if env.rebind_inner {
                        let mut ycx = acx.clone();
                        ycx.push("#y".into(), a.clone(), lp.clone());
                        ind.index_ty
                            .as_ref()
                            .and_then(|ity| self.index_head(&ycx, ity, &c, span))
                            .and_then(|(_, args)| args.first().map(|a| Rc::new((**a).clone())))
                    } else {
                        Some(Rc::new(c.clone()))
                    };
                    fn_children.push(FnChildIh {
                        fun: Rc::new(k_term.clone()),
                        ih: Rc::new(ih),
                        ih_ty,
                        rebind,
                    });
                    (k_term, pi(lp, &fl, a, sigd.fam(by + 1, &c)), join(lp, &fl))
                }
            };
            acx.aliases.push(Rc::new(Alias {
                skel: None,
                name,
                depth,
                term: Rc::new(term),
                ty,
                level,
                spliced: None,
            }));
        }
        if !children.is_empty() || !fn_children.is_empty() {
            acx.guard = env
                .dec
                .map(|dec| {
                    Rc::new(Guard {
                        dec,
                        kind: GuardKind::Wf {
                            depth: acx.names.len(),
                            children,
                            container: None,
                            fn_children,
                            // Not chain-shaped for the window's purposes.
                            cov: None,
                        },
                        rebind: env.idx_param.map(|p| (p, rebind)),
                        generalized: crate::generalize::guard_gen(&acx, dec, None),
                    })
                })
                .or_else(|| env.outer_guard.clone());
        }
        Ok(acx)
    }
}

/// Child `t`'s tree, fact and ih head (the ih applied to its position) at
/// `y`, `e` binders past the arm's context (one for a function field's `y`),
/// which is itself `by` past `B`.
fn arm_piece(br: &Br, kids_in: &ArmKids, t: usize, y: Term, e: u32, by: u32) -> (Term, Term, Term) {
    let at = by + e;
    let is_fn = br.kids[t].dom.is_some();
    match kids_in {
        ArmKids::One { f, ih, cs } => {
            let tree = app(f.shift_local(e), br.inj(t, y.clone(), at));
            let fact = if is_fn { app(cs.shift_local(e), y.clone()) } else { cs.shift_local(e) };
            (tree, fact, app(ih.shift_local(e), br.inj(t, y, at)))
        }
        ArmKids::Many { kbar, ih, cs } => {
            let kb = kbar.shift_local(e);
            let tree = br.k_at(&kb, t, y.clone(), at);
            let items = br.ch_items(&br.rho(&kb, at), at);
            let cst = proj(&items, t, cs.shift_local(e));
            let fact = if is_fn { app(cst, y.clone()) } else { cst };
            (tree, fact, app(ih.shift_local(e), br.inj(t, y, at)))
        }
    }
}

/// How an arm reaches its children (§7's table).
enum ArmKids {
    /// One recursive field: the tree's children `f'` themselves, the ih `ih'`
    /// and the fact `cs`.
    One { f: Term, ih: Term, cs: Term },
    /// Two or more: the stored children `k̄`, the generalized ih and the
    /// facts `cs`.
    Many { kbar: Term, ih: Term, cs: Term },
}

/// The levels of `match`'s motive pieces (§7), and the pieces themselves.
struct MatchLevels {
    /// `M'`'s.
    lmp: Level,
    /// The step ih's.
    lih: Level,
    qin: Level,
    lq: Level,
}

impl MatchLevels {
    fn new(sig: &IwSig, mlvl: &Level) -> MatchLevels {
        let lmp = join(&sig.ilvl, &join(&sig.lk, mlvl));
        let lih = join(&sig.lp, &lmp);
        let qin = join(&lih, &lmp);
        let lq = join(&sig.lf(), &qin);
        MatchLevels { lmp, lih, qin, lq }
    }

    /// `M'(w) = Π(j : I). Π(c : El(ok w j)). M(j, ⟨w, c⟩)`, `by` past the
    /// context `sig` is scoped in, which is `base` past Γ.
    fn m_prime(&self, env: &ArmEnv, sig: &IwSig, base: u32, by: u32, w: &Term) -> Type {
        let (li, lk, mlvl) = (&sig.ilvl, &sig.lk, env.mlvl);
        pi(
            li,
            &join(lk, mlvl),
            sig.ity.shift_local(by),
            pi(
                lk,
                mlvl,
                sig.ok_ty(by + 1, &w.shift_local(1), &var(0)),
                env.mot_at(var(1), sig.pair(by + 2, &var(1), w.shift_local(2), var(0)), base + by + 2),
            ),
        )
    }

    /// `Π(p : P v). M'(f p)`, the step's ih.
    fn ih_ty(&self, env: &ArmEnv, sig: &IwSig, base: u32, by: u32, v: &Term, f: &Term) -> Type {
        pi(
            &sig.lp,
            &self.lmp,
            sig.pos_at(by, v),
            self.m_prime(env, sig, base, by + 1, &app(f.shift_local(1), var(0))),
        )
    }

    /// `Q(v) = Π(f'). Π(ih' : Π(p : P v). M'(f' p)). M'(sup(v; f'))`.
    fn q(&self, env: &ArmEnv, sig: &IwSig, base: u32, by: u32, v: &Term) -> Type {
        pi(
            &sig.lf(),
            &self.qin,
            sig.kids_ty(by, v),
            pi(
                &self.lih,
                &self.lmp,
                self.ih_ty(env, sig, base, by + 1, &v.shift_local(1), &var(0)),
                self.m_prime(env, sig, base, by + 2, &sig.sup(by + 2, v.shift_local(2), var(1))),
            ),
        )
    }
}
