//! An `elim_Wf` induction hypothesis spelled as the call it is the
//! recursion of (issues/wide-inductive-lemma-quadratic-gate.md).
//!
//! A structurally recursive `fn g(…, t: D, …)` lowers to `λ x̄. elim_Wf(…;
//! M; s; x_t) x_j…`, whose step `s` holds one arm per constructor of `D`.
//! Unfolding `g(ā)` at a constructor fires that eliminator, and the kernel's
//! ι-rule (`reduce.rs`) spells the induction hypothesis as `λ i.
//! elim_Wf(…; s; nth(cs; i))`: a copy of the whole step. The elaborator reads
//! such reducts back as syntax — a reduct walk's head, a whnf's readback — and
//! a unifier solution or a reduced goal built from one carries the copy into
//! the declaration, where the gate checks it again. One copy per arm is a
//! case tree of `n` arms per arm: the `n²` of a lemma by cases over an
//! `n`-constructor syntax.
//!
//! The hypothesis is the same function as `λ i q̄. g(…, nth(cs; i), q̄, …)` up
//! to δ, so that is how it is spelled here, in constant size. Nothing is
//! trusted: the eliminator is refolded only when its fields are, node for
//! node, the ones `g`'s body holds at the call's fixed arguments, with the
//! descended and varied parameters standing in as locals no context reaches
//! (so a field that read one of them refuses), and the gate checks the
//! result as it checks any term.

use std::cell::RefCell;
use std::collections::HashMap;
use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::reduce::Defs;
use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type, nth};

use crate::spelling;

/// The fields of an `elim_Wf` that fires, at the walk's Γ.
pub(crate) struct WfElim<'a> {
    pub(crate) level: &'a Level,
    pub(crate) motive_level: &'a Level,
    pub(crate) shape: &'a Rc<Type>,
    pub(crate) arity: &'a Rc<Term>,
    pub(crate) motive: &'a Rc<Type>,
    pub(crate) step: &'a Rc<Term>,
}

/// A definition body's parameters read as a structural recursion: `m` λs
/// over `elim_Wf(…; x_s) x_{varied[0]} …`.
pub(crate) struct Layout {
    m: usize,
    s: usize,
    varied: Vec<usize>,
}

impl Layout {
    /// `body`'s layout and the eliminator under its λs (scoped under them),
    /// when `body` is a structural recursion's lowering.
    pub(crate) fn of_body(body: &Term) -> Option<(Layout, &Term)> {
        let mut m = 0usize;
        let mut inner = body;
        while let Term::Lam { body, .. } = inner {
            m += 1;
            inner = body;
        }
        let (head, spine) = spelling::app_spine(inner);
        let Term::ElimWf { scrut, .. } = head else {
            return None;
        };
        // Parameter `p` (0-based, outermost first) is `Var(m - 1 - p)` here.
        let param = |t: &Term| match t {
            Term::Var(LocalVar(i)) if (*i as usize) < m => Some(m - 1 - *i as usize),
            _ => None,
        };
        let s = param(scrut)?;
        let varied: Vec<usize> = spine.iter().map(|a| param(a)).collect::<Option<_>>()?;
        let mut seen = vec![false; m];
        for &p in std::iter::once(&s).chain(&varied) {
            if std::mem::replace(&mut seen[p], true) {
                return None;
            }
        }
        Some((Layout { m, s, varied }, head))
    }

    /// The number of parameters the body abstracts.
    pub(crate) fn params(&self) -> usize {
        self.m
    }

    /// Is parameter `p` one the recursion fixes (neither descended on nor
    /// varied)? Only those arguments are read.
    pub(crate) fn fixed(&self, p: usize) -> bool {
        p != self.s && !self.varied.contains(&p)
    }

    /// `elim` (scoped under the body's λs, in Γ past them) at the call's
    /// arguments, the unfixed ones as [`unreachable_local`]s.
    fn instantiate(&self, gamma: &LocalCtx, elim: &Term, args: &[Rc<Term>]) -> Term {
        let mut delta = LocalSubst::id(gamma);
        for (p, a) in args.iter().take(self.m).enumerate() {
            delta = delta.extended(if self.fixed(p) { Rc::clone(a) } else { unreachable_local(p) });
        }
        elim.apply_local(&delta)
    }

    /// Whether `elim`, instantiated at `args`, has exactly `fields`.
    pub(crate) fn matches(&self, gamma: &LocalCtx, elim: &Term, args: &[Rc<Term>], fields: &WfElim<'_>) -> bool {
        if args.len() < self.m {
            return false;
        }
        let Term::ElimWf { level, motive_level, shape, arity, motive, step, .. } = self.instantiate(gamma, elim, args)
        else {
            return false;
        };
        level == *fields.level
            && motive_level == *fields.motive_level
            && shape == *fields.shape
            && arity == *fields.arity
            && motive == *fields.motive
            && step == *fields.step
    }

    /// The hypothesis of this recursion's eliminator firing on `sup_f(…;
    /// label; children)` at Γ, as calls of `head` (the global, at Γ) at
    /// `args` (only the fixed ones are read): `λ(i : Fin n[a/x]). λ q̄.
    /// g(…, nth(cs; i), q̄, …)`. The caller has established that the
    /// eliminator is this recursion's at `args` ([`Self::matches`]).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn refolded_ih(
        &self,
        head: &Term,
        args: &[Rc<Term>],
        level: &Level,
        motive_level: &Level,
        shape: &Rc<Type>,
        arity_at: Term,
        arity: &Rc<Term>,
        motive: &Type,
        children: &Term,
    ) -> Option<Term> {
        if args.len() < self.m {
            return None;
        }
        let wf = Type::Wf { level: level.clone(), shape: Rc::clone(shape), arity: Rc::clone(arity) };
        let child = nth(
            level,
            &Rc::new(wf.shift_local(1)),
            &Rc::new(arity_at.shift_local(1)),
            Rc::new(children.shift_local(1)),
            Rc::new(Term::Var(LocalVar(0))),
        );
        let mut binders = Vec::with_capacity(self.varied.len());
        let mut goal = motive.inst_top(1, &child);
        for _ in &self.varied {
            let Type::Pi { dom_level, cod_level, dom, cod } = goal else {
                return None;
            };
            binders.push((dom_level, cod_level, dom));
            goal = (*cod).clone();
        }
        let r = self.varied.len() as u32;
        let mut call = head.shift_local(1 + r);
        for (p, a) in args.iter().take(self.m).enumerate() {
            let a = if p == self.s {
                child.shift_local(r)
            } else if let Some(l) = self.varied.iter().position(|&q| q == p) {
                Term::Var(LocalVar(r - 1 - l as u32))
            } else {
                a.shift_local(1 + r)
            };
            call = Term::AppAt { fun: Rc::new(call), arg: Rc::new(a) };
        }
        for (dom_level, cod_level, dom) in binders.into_iter().rev() {
            call = Term::Lam { dom_level, cod_level, dom, body: Rc::new(call) };
        }
        Some(Term::Lam {
            dom_level: Level::Zero,
            cod_level: motive_level.clone(),
            dom: Rc::new(Type::Fin { len: Rc::new(arity_at) }),
            body: Rc::new(call),
        })
    }
}

/// The body of `var` as Ψ stores it (in its own prefix), when `var` is a
/// definition this world unfolds and an occurrence with `payloads` entries
/// fits its context.
pub(crate) fn stored_body(world: &GlobalCtx, var: GlobalVar, payloads: usize) -> Option<&Rc<Term>> {
    if Defs::transparent(world).withheld(var).is_some() {
        return None;
    }
    let at = var.position(world.bindings.len())?;
    match world.bindings.get(at)? {
        GlobalBinding::Tm { body: Some(body), ctx, .. } if ctx.entries.len() == payloads => Some(body),
        _ => None,
    }
}

/// Is `step` (by identity) the step of the eliminator in `body`, a stored
/// definition body? What a value's eliminator is checked against before its
/// definition is read as a [`Layout`]: only that node evaluates to a closure
/// over that step.
pub(crate) fn holds_step(body: &Term, step: &Rc<Term>) -> bool {
    let mut inner = body;
    while let Term::Lam { body, .. } = inner {
        inner = body;
    }
    matches!(spelling::app_spine(inner).0, Term::ElimWf { step: s, .. } if Rc::ptr_eq(s, step))
}

thread_local! {
    /// Stored definition bodies whose eliminator a readback has compared in
    /// full ([`Layout::matches`]) once, keyed by the body's address, with the
    /// verdict. Each entry holds its body, so an address is never reused
    /// while it is a key. Bounded: past the cap the table starts over.
    static VERIFIED: RefCell<HashMap<usize, (Rc<Term>, bool)>> = RefCell::new(HashMap::new());
}

const VERIFIED_CAP: usize = 4096;

/// The verdict recorded for `body` ([`record_verdict`]), if any.
///
/// A value's eliminator whose step is the stored node's ([`holds_step`])
/// was built by evaluating that node, so its fields are the body's under
/// the environment the definition's λs bound. Whether they read only the
/// fixed parameters is a fact about the body, decided the first time by
/// the full comparison; after that, the identity is the comparison.
pub(crate) fn verdict(body: &Rc<Term>) -> Option<bool> {
    VERIFIED.with(|v| v.borrow().get(&(Rc::as_ptr(body) as usize)).map(|(_, ok)| *ok))
}

/// Record `ok` as `body`'s verdict ([`verdict`]).
pub(crate) fn record_verdict(body: &Rc<Term>, ok: bool) {
    VERIFIED.with(|v| {
        let mut v = v.borrow_mut();
        if v.len() >= VERIFIED_CAP {
            v.clear();
        }
        v.insert(Rc::as_ptr(body) as usize, (Rc::clone(body), ok));
    });
}

/// The ι-step of `current`'s head `elim_Wf` on a `sup_f`, with the
/// induction hypothesis spelled as calls of `call`'s head: `call` is
/// `g(ā)`, the walk's last reduct headed by a defined global, and the firing
/// eliminator must be the one `g`'s body holds at `ā`. `None` whenever it is
/// not: the kernel's own step is then taken.
pub(crate) fn refolded_fire(world: &GlobalCtx, gamma: &LocalCtx, call: &Term, current: &Term) -> Option<Term> {
    let Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } = spelling::app_spine(current).0 else {
        return None;
    };
    let Term::Supf { label, children, .. } = &**scrut else {
        return None;
    };
    let (g, args) = spelling::app_spine(call);
    let Term::GlobalTm { var, subst } = g else {
        return None;
    };
    let stored = stored_body(world, *var, subst.terms.len())?;
    Layout::of_body(stored)?;
    let body = stored.shift_global(var.rescope()).apply_local(subst);
    let (layout, elim) = Layout::of_body(&body)?;
    let args: Vec<Rc<Term>> = args.into_iter().cloned().collect();
    let fields = WfElim { level, motive_level, shape, arity, motive, step };
    if !layout.matches(gamma, elim, &args, &fields) {
        return None;
    }
    let arity_at = arity.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(label)));
    let ih = layout.refolded_ih(g, &args, level, motive_level, shape, arity_at, arity, motive, children)?;
    let delta = LocalSubst::id(gamma).extended(Rc::clone(label)).extended(Rc::clone(children)).extended(Rc::new(ih));
    Some(with_spine_head(current, step.apply_local(&delta)))
}

/// `t`'s application spine with its head replaced by `head`.
fn with_spine_head(t: &Term, head: Term) -> Term {
    match t {
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => Term::App {
            fun: Rc::new(with_spine_head(fun, head)),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
            arg: Rc::clone(arg),
        },
        Term::AppAt { fun, arg } => Term::AppAt { fun: Rc::new(with_spine_head(fun, head)), arg: Rc::clone(arg) },
        _ => head,
    }
}

/// A stand-in for a parameter the recursion descends on or varies, while
/// the eliminator a body holds is instantiated at a call: a local no context
/// reaches, so a field that read the parameter differs from the reduct's.
fn unreachable_local(p: usize) -> Rc<Term> {
    Rc::new(Term::Var(LocalVar((1 << 30) + p as u32)))
}
