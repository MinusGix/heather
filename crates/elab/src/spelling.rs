//! Reading a pair, an injection or a projection **whichever spelling it is
//! written in** (`docs/intro-by-type-design.md` §4.2).
//!
//! Since stage 1 the kernel has five *checked spellings* —
//! `pair@`/`inl@`/`inr@`/`fst@`/`snd@` — that carry the type the term was
//! checked at in place of that type's components. They are the same terms:
//! the evaluator maps them onto the same values, β fires on either, and
//! conversion never reads either one's annotation. So every **shape-only**
//! reader in the elaborator — the ones that ask "is this an injection, and
//! into which summand" or "what are this tuple's fields" — must accept both,
//! and the three views here are how, rather than by a doubled `match` arm at
//! forty sites.
//!
//! A reader that genuinely needs the *components* (`lgg`'s anti-unification,
//! `matching`'s `field_rewrap`) is not served here: it has a decision to make
//! about the annotation and must make it in the open. The principle from
//! §4.2 stands for both kinds — the annotation is a spelling every reader
//! already accepts from a user-written type, so a broken reader is fixed in
//! the reader.

use heather_kernel::rc::Rc;
use std::collections::HashMap;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};

/// The injected value of either injection spelling, with `true` for `inl`.
pub(crate) fn inj_of(t: &Term) -> Option<(bool, &Rc<Term>)> {
    match t {
        Term::Inl { val, .. } | Term::InlAt { val, .. } => Some((true, val)),
        Term::Inr { val, .. } | Term::InrAt { val, .. } => Some((false, val)),
        _ => None,
    }
}

/// Where a constructor value's injection path leads ([`inj_path`]).
pub(crate) struct InjPath<'t> {
    /// The constructor the path selects; when it stopped short, the first
    /// constructor of the `+` it stopped at.
    pub(crate) ctor: usize,
    /// The payload, or the term the path stopped at (no injection: a
    /// neutral, or a value that is not a constructor at all).
    pub(crate) at: &'t Term,
    /// Whether the path reached a payload.
    pub(crate) reached: bool,
    /// `at` as the last injection's own value, when the path crossed one
    /// (`at` is the label itself otherwise).
    pub(crate) val: Option<&'t Rc<Term>>,
    /// Whether it crossed any injection.
    pub(crate) injected: bool,
}

/// Walk a value of an `n`-constructor sum down its injections, the `+` tree
/// being the one [`crate::sum_layout`] decides: each injection picks a side,
/// until a payload. Either injection spelling — this reads the *path*, never
/// an annotation, so `inr@` is an `inr`.
pub(crate) fn inj_path<'t>(label: &'t Term, n: usize) -> InjPath<'t> {
    use crate::sum_layout::Child;
    let layout = crate::sum_layout::layout(n);
    let (mut at, mut cur, mut last) = (layout.root(), label, None);
    let path = |ctor, at, reached, val: Option<&'t Rc<Term>>| InjPath { ctor, at, reached, val, injected: val.is_some() };
    loop {
        match at {
            None => return path(0, cur, false, last),
            Some(Child::Leaf(k)) => return path(k, cur, true, last),
            Some(Child::Node(j)) => {
                let node = layout.node(j);
                let Some((left, val)) = inj_of(cur) else {
                    return path(node.lo, cur, false, last);
                };
                at = Some(node.side(!left));
                cur = val;
                last = Some(val);
            }
        }
    }
}

/// The two components of either pair spelling.
pub(crate) fn pair_of(t: &Term) -> Option<(&Rc<Term>, &Rc<Term>)> {
    match t {
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => Some((fst, snd)),
        _ => None,
    }
}

/// Is this a pair, in either spelling?
pub(crate) fn is_pair(t: &Term) -> bool {
    matches!(t, Term::Pair { .. } | Term::PairAt { .. })
}

/// Is this an injection, in either spelling?
pub(crate) fn is_inj(t: &Term) -> bool {
    matches!(
        t,
        Term::Inl { .. } | Term::Inr { .. } | Term::InlAt { .. } | Term::InrAt { .. }
    )
}

/// The pair a projection projects, with `true` for `fst`.
pub(crate) fn proj_of(t: &Term) -> Option<(bool, &Rc<Term>)> {
    match t {
        Term::Fst { pair, .. } | Term::FstAt { pair, .. } => Some((true, pair)),
        Term::Snd { pair, .. } | Term::SndAt { pair, .. } => Some((false, pair)),
        _ => None,
    }
}

/// The component a projection chain reads off a pair it is written over,
/// by syntax alone: `fst(snd(pair(a; pair(b; c))))` is `b`. A field read
/// off a constructed record (`CdState(s.m - 1, …).m`, a `decreases`
/// measure at a self-call's argument) is this shape, and its component is
/// the field's value with no δ step taken — where a weak head would unfold
/// the value on into its definition's eliminator
/// (issues/decreases-measure-record-field-unspelled.md). `None` unless every
/// projection meets a pair.
pub(crate) fn project_value(t: &Term) -> Option<&Rc<Term>> {
    let (first, pair) = proj_of(t)?;
    let inner: &Term = if proj_of(pair).is_some() { project_value(pair)? } else { pair };
    let (a, b) = pair_of(inner)?;
    Some(if first { a } else { b })
}

/// `t` with every projection of a literal pair read off the pair, wherever
/// it sits among the formers a reduct's fields are built of.
///
/// A weak head reached through the checked spelling carries such redexes in
/// its arguments: a `match` arm binds a component of an intro written bare
/// (`docs/codata-named-signature-design.md` §5), and the arm's own `fst@`/
/// `snd@` of that binder is what the reduct substitutes it into. The kernel
/// infers a projection's receiver, and a bare `pair@` does not infer, so the
/// reduct is a term the kernel refuses with `NotInferable` wherever it is
/// emitted (issues/kernel-refuses-inj-through-corecursive-reduct.md).
/// Reading the component off is Σ's own β rule, so the result is convertible
/// with `t`, and it only removes nodes, so no scope moves and nothing is
/// shifted. Types are left whole: their term slots are the annotations the
/// spelling kept, and a reduct's types are not where it put a redex. Shares
/// every untouched subtree.
///
/// A reduct is a graph: a record updated field by field is each update's
/// record built from projections of the one before, so the walk visits a
/// node once however many parents it has. Walked as a tree, such a term
/// costs its fields to the power of its updates.
pub(crate) fn contract_projections(t: &Rc<Term>) -> Rc<Term> {
    contract_projections_once(t, 0, &mut HashMap::new())
}

/// [`contract_projections`], with the answers of the nodes more than one
/// parent can reach: those with more owners than their parent and the
/// `held` copies of it the walk itself made. Every key is a node of the
/// term the walk began at, which outlives the walk, so no address is reused
/// under it.
fn contract_projections_once(t: &Rc<Term>, held: usize, seen: &mut HashMap<*const Term, Rc<Term>>) -> Rc<Term> {
    if Rc::strong_count(t) <= 1 + held {
        return contract_projections_at(t, seen);
    }
    if let Some(done) = seen.get(&Rc::as_ptr(t)) {
        return Rc::clone(done);
    }
    let out = contract_projections_at(t, seen);
    seen.insert(Rc::as_ptr(t), Rc::clone(&out));
    out
}

fn contract_projections_at(t: &Rc<Term>, seen: &mut HashMap<*const Term, Rc<Term>>) -> Rc<Term> {
    if let Some((first, pair)) = proj_of(t) {
        let inner = contract_projections_once(pair, 0, seen);
        if let Some((a, b)) = pair_of(&inner) {
            return Rc::clone(if first { a } else { b });
        }
        if Rc::ptr_eq(&inner, pair) {
            return Rc::clone(t);
        }
        let mut out = (**t).clone();
        match &mut out {
            Term::Fst { pair, .. } | Term::FstAt { pair, .. } | Term::Snd { pair, .. } | Term::SndAt { pair, .. } => {
                *pair = inner;
            }
            _ => unreachable!("proj_of matched a projection"),
        }
        return Rc::new(out);
    }
    // Every term child of the formers below, rewritten in place, and `false` when
    // none moved. The slots are a copy's, so each child has one owner more.
    fn each(slots: &mut [&mut Rc<Term>], seen: &mut HashMap<*const Term, Rc<Term>>) -> bool {
        let mut moved = false;
        for slot in slots.iter_mut() {
            let new = contract_projections_once(slot, 1, seen);
            if !Rc::ptr_eq(&new, slot) {
                **slot = new;
                moved = true;
            }
        }
        moved
    }
    let mut out = (**t).clone();
    let moved = match &mut out {
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => each(&mut [fst, snd], seen),
        Term::Inl { val, .. } | Term::Inr { val, .. } | Term::InlAt { val, .. } | Term::InrAt { val, .. } => {
            each(&mut [val], seen)
        }
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => each(&mut [fun, arg], seen),
        Term::Lam { body, .. } => each(&mut [body], seen),
        Term::Succ(n) => each(&mut [n], seen),
        Term::Refl { tm, .. } => each(&mut [tm], seen),
        Term::Supf { label, children, .. } => each(&mut [label, children], seen),
        Term::Corec { index, seed, .. } => each(&mut [index, seed], seen),
        Term::Out { index, scrut, .. } => each(&mut [index, scrut], seen),
        Term::Case { case_l, case_r, scrut, .. } => each(&mut [case_l, case_r, scrut], seen),
        _ => false,
    };
    if moved { Rc::new(out) } else { Rc::clone(t) }
}

/// Compare a projection path without comparing its typing annotations.
/// Arm aliases and motive instantiations carry different emitted spellings
/// of the same Σ types.
pub(crate) fn same_projection(a: &Term, b: &Term) -> bool {
    match (proj_of(a), proj_of(b)) {
        (Some((af, ap)), Some((bf, bp))) => af == bf && same_projection(ap, bp),
        _ => a == b,
    }
}

/// Read a constructor tuple, recovering neutral fields from the typed arm
/// aliases. In the Wf lowering an alias is an `nth` call; bounded reduction
/// exposes the same projection path. Returning that alias's original term
/// preserves both its type and its surface spelling. `under` is the display
/// walk's extra binder depth: reduction happens in `cx` before weakening,
/// so the oracle never receives a term outside its context.
pub(crate) fn tuple_fields(
    elab: &crate::Elaborator,
    cx: &crate::Cx,
    tuple: &Term,
    skip: usize,
    count: usize,
    under: u32,
) -> Option<Vec<Rc<Term>>> {
    let mut cur = Rc::new(tuple.clone());
    for _ in 0..skip {
        cur = match pair_of(&cur) {
            Some((_, snd)) => Rc::clone(snd),
            None => Rc::new(Term::SndAt { pair: cur }),
        };
    }
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        if let Some((fst, snd)) = pair_of(&cur) {
            out.push(Rc::clone(fst));
            cur = Rc::clone(snd);
            continue;
        }
        let field = Term::FstAt { pair: Rc::clone(&cur) };
        let alias = cx.aliases.iter_inner().find_map(|a| {
            let shift = cx.names.len().checked_sub(a.depth)? as u32;
            let term = Rc::new(a.term.shift_local(shift));
            let shifted = Rc::new(term.shift_local(under));
            if same_projection(&field, &shifted) {
                return Some(shifted);
            }
            // `nth` is headed by Nat elimination. Ordinary let-bound
            // function calls cannot be arm children and need no evaluation.
            if matches!(app_spine(&term).0, Term::ElimNat { .. }) {
                let reduced = elab.goal_oracle().whnf_term_bounded(&cx.gamma, &term).ok()?;
                if same_projection(&field, &reduced.shift_local(under)) {
                    return Some(shifted);
                }
            }
            None
        })?;
        out.push(alias);
        cur = Rc::new(Term::SndAt { pair: cur });
    }
    Some(out)
}

/// The head and argument of either application spelling — `app` with its
/// annotations or the checked `app@(f; a)`, whose Π is the one the head
/// infers (`docs/app-by-head-type-design.md` §6.2). A reader that needs the
/// Π itself has a decision to make and does not come here.
pub(crate) fn app_of(t: &Term) -> Option<(&Rc<Term>, &Rc<Term>)> {
    match t {
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => Some((fun, arg)),
        _ => None,
    }
}

/// Is this an application, in either spelling?
pub(crate) fn is_app(t: &Term) -> bool {
    matches!(t, Term::App { .. } | Term::AppAt { .. })
}

/// `f a₁ … aₙ` as its head and its arguments, outermost last, through
/// either spelling at every node.
pub(crate) fn app_spine(t: &Term) -> (&Term, Vec<&Rc<Term>>) {
    let mut args = Vec::new();
    let mut head = t;
    while let Some((fun, arg)) = app_of(head) {
        args.push(arg);
        head = fun;
    }
    args.reverse();
    (head, args)
}

/// `t` with the β-redexes at the head of its spine contracted, `(λx. b) s ⋯`
/// to `b[s/x] ⋯`, until the head is no λ; `None` when there was none. Only
/// the head: an argument's redexes are reached when the congruence gets to
/// them.
pub(crate) fn beta_head(t: &Term) -> Option<Term> {
    let (fun, arg) = app_of(t)?;
    let r = match &**fun {
        Term::Lam { body, .. } => body.inst_top(0, arg),
        _ => {
            let fun = Rc::new(beta_head(fun)?);
            match t {
                Term::App { dom_level, cod_level, dom, cod, arg, .. } => Term::App {
                    fun,
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: Rc::clone(dom),
                    cod: Rc::clone(cod),
                    arg: Rc::clone(arg),
                },
                _ => Term::AppAt { fun, arg: Rc::clone(arg) },
            }
        }
    };
    Some(beta_head(&r).unwrap_or(r))
}

/// `ty` with its `El` term's head β-redexes contracted ([`beta_head`]);
/// `None` when there was none. A pattern-bound proof is typed so: an
/// `Exists`'s `.proof` is `(λ k => P(k))(e.witness)`, read raw no relation is
/// visible in it (issues/omega-redex-typed-fact-ignored.md,
/// issues/linarith-redex-typed-fact.md).
pub(crate) fn beta_head_ty(ty: &Type) -> Option<Type> {
    match ty {
        Type::El { level, tm } => Some(Type::El { level: level.clone(), tm: Rc::new(beta_head(tm)?) }),
        _ => None,
    }
}

/// An application the elaborator **constructs** from a Π it holds, outside
/// the surface-call path (`docs/app-by-head-type-design.md` §6.1, every
/// emitter switched): `app@(f; a)` unless the head is a λ, which infers only
/// if its body does and so keeps the annotated form. The annotations are
/// taken so a call site reads as the `app` it replaces and are dropped for
/// `app@`: its Π is the one the head infers.
///
/// Unconditional on the quotation state, because none of these builders
/// writes a `box` payload itself: a term pasted into a quotation goes through
/// the quote boundary's translator (`typing::spell_checked_in_code`), which
/// writes `app` back from the Π the checker read. Code that is *built* as a
/// payload (certgen's markers, the code recursor's branches) writes `app`.
pub(crate) fn checked_app(
    fun: Rc<Term>,
    dom_level: Level,
    cod_level: Level,
    dom: Rc<Type>,
    cod: Rc<Type>,
    arg: Rc<Term>,
) -> Term {
    if matches!(&*fun, Term::Lam { .. }) {
        Term::App { fun, dom_level, cod_level, dom, cod, arg }
    } else {
        Term::AppAt { fun, arg }
    }
}
