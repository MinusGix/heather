//! Implicit-application scratch state and state-free structural unification.

use std::cell::{Cell, RefCell};
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{CtxBase, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type};
use heather_syntax::Expr;

use crate::{code, inductive, spelling};

/// A deferred explicit argument (docs/unifier-completeness-design.md §3.1):
/// **not** a first-class constraint in a queue on the [`crate::Elaborator`],
/// but a record local to one [`crate::application::apply_implicit`] activation.
/// The scratch world is the constraint store — the domain's meta occurrences
/// *are* the "blocked on" set, and [`zonked`] decides readiness exactly.
/// Cross-call postponement is deliberately not built: a nested call elaborates
/// to completion (or errors) inside its own world before the outer loop
/// continues, so there is nothing an inner call could leave pending that the
/// outer call could later unblock.
pub(crate) struct ResolveOb {
    /// The scratch slot standing for the argument.
    pub(crate) slot: usize,
    /// The parameter's declared domain, scratch world — the goal, once every
    /// meta it mentions is solved (docs/traits-layer2-design.md §4).
    pub(crate) dom: Type,
    pub(crate) dom_level: Level,
    /// Parameter index, for the hint and the message.
    pub(crate) param: usize,
    /// The application as built up to this parameter, scratch world: its
    /// leading arguments are the callee's type arguments, which is where a
    /// solver parameter's carrier lives once its type parameter is solved
    /// ([`Elaborator::solver_carrier_head`]). `None` where no application
    /// was being built.
    pub(crate) applied: Option<Term>,
}

pub(crate) struct DeferredArg<'a> {
    /// The withheld slot: the stand-in meta holding the argument's spine
    /// position.
    pub(crate) slot: usize,
    /// The unelaborated surface argument.
    pub(crate) expr: &'a Expr,
    /// Its declared domain, scratch world.
    pub(crate) dom: Type,
    pub(crate) dom_level: Level,
    /// Parameter index, for the goal-name hint and the §7.2 message.
    pub(crate) param: usize,
    /// This argument prefers checking but has a compatibility inference
    /// route: a result-only implicit call or a fully annotated lambda.
    /// If its domain never becomes ready, inference may supply the missing
    /// type information (or the original inference error). An annotated
    /// lambda's body can still be checking-only, so expected-type solving
    /// and ready obligations run before this fallback.
    pub(crate) fallback_infer: bool,
    /// Deferred only because its inference failed while this domain waited
    /// on the call's implicits ([`crate::application::apply_implicit`]'s
    /// re-plan). If the domain never resolves, the fallback's error is about
    /// the implicit nothing pinned, not the argument.
    pub(crate) replanned: bool,
    /// For an omitted default's marker, the call's arguments before it, in
    /// the scratch world: a default that mentions an earlier parameter waits
    /// for that argument as well as for its domain. Empty for every other
    /// argument.
    pub(crate) earlier: Vec<EarlierArg>,
}

/// One argument a call gave before a defaulted parameter, for a default that
/// mentions its parameter (`k: Nat := n`; docs/named-arguments-design.md
/// §9.6): the parameter's index in the callee's table, the argument, and its
/// type, which is the parameter's domain as this call instantiated it.
#[derive(Clone)]
pub(crate) struct EarlierArg {
    pub(crate) param: usize,
    pub(crate) term: Rc<Term>,
    pub(crate) ty: Type,
    pub(crate) level: Level,
}

/// Per-slot state of one [`crate::application::apply_implicit`] scratch world
/// (docs/unifier-completeness-design.md §3). Three states, because two
/// different "unsolved" populations exist and must not be conflated:
///
/// - `Unsolved` — nothing known yet; `unify_ty`/`unify_tm` may record a
///   solution here (and only here).
/// - `Withheld` — unsolved *and untouchable*: a deferred argument's stand-in
///   meta, or a flex-applied meta during the LGG's harvest. [`zonked`] treats
///   it as unsolved (its occurrences must keep blocking dependent domains),
///   while the unifiers refuse to write into it. This replaces the old
///   plant-a-`Term::Zero` placeholder, which made a withheld slot *look*
///   solved to `zonked` — a lie once deferred arguments joined the world.
/// - `Solved(t)` — `t` is a committed-world payload, the convention the
///   unifiers' strengthened subjects already follow.
///
/// Discharge requires `Solved` everywhere; anything else is a per-slot
/// diagnostic (design §7).
#[derive(Clone)]
pub(crate) enum Sol {
    Unsolved,
    Withheld,
    Solved(Rc<Term>),
}

impl Sol {
    pub(crate) fn solved(&self) -> Option<&Rc<Term>> {
        match self {
            Sol::Solved(t) => Some(t),
            _ => None,
        }
    }
}

/// Best-effort structural unification driving implicit-argument solutions
/// (issues/elab-stage2-metas.md). `pat` is a parameter domain in the scratch
/// world (metavariables at Ψ-indices `< n`); `subj` is an argument's inferred
/// type. Solving is deliberately incomplete: this mirrors the fragment of
/// `conv.rs` the Nat suite exercises (`Id`/`Nat` congruence), records a
/// solution whenever a meta meets a rigid subterm, and otherwise makes no
/// claim — an unsolved meta is reported by the caller, a *wrong* solution is
/// caught by the kernel's re-check. It never fails: it only ever *learns*.
/// Congruence through every type former the lowerings build, plus the one
/// rule that makes polymorphism inferable:
///
/// > `El ?A ≟ T` solves `?A := ⌜T⌝` (docs/surface-polymorphism.md §4).
///
/// `d` counts the binders crossed since `gamma` — a `Σ`'s second component, a
/// `Π`'s codomain, a `Wf`'s arity. A meta's solution is scoped in `gamma`, so
/// a candidate found under `d` binders is accepted only if it survives
/// [`strengthen_ty`]. Without that check `f(g)` at `g : (x : Nat) -> Vec(A;
/// x)` would happily solve a meta to a term mentioning `x`, which is
/// ill-scoped where it lands (the kernel would reject it, but a rejection is
/// a worse message than a refusal to guess).
/// What the syntactic congruence is run against: the scope a solution lands
/// in, and the one question it cannot answer from syntax alone.
///
/// `type_args` answers, for a rigid application spine in the subject under
/// `d` binders, which of its arguments sit at a `Ty` domain — the spine's
/// parameter telescope read off its **head's** type. An `app(…)` node
/// states its domain, but `app@(f; a)` (`docs/app-by-head-type-design.md`
/// §6.2) does not, so [`matching_value_spine`] asks here for those. `None`
/// is "cannot read it", and the spine is then not a matching value spine,
/// which is the refusal the rule already gave a head it could not read.
///
/// `canonical_head` is the one reduction the unifier may ask for: the weak
/// head of a rigid subject term, `d` binders past `gamma`, returned only when
/// it is a canonical form — a successor or numeral, a `sup`/`supf`, a pair or
/// an injection. `Succ(?n)` against `m + Succ(k)` has nothing to align until
/// `Nat::add` takes its step (issues/unify-succ-under-addition.md), and
/// `Cons(?r, ?rt)` against `rr_bytes(…)` nothing until the definition unfolds
/// (issues/unify-through-constructor-values.md). Asked only where such a
/// pattern meets a subject headed by a global, the one kind δ can unfold,
/// so every pairing that learned before learns the same without it.
pub(super) struct U<'a> {
    pub(super) gamma: &'a LocalCtx,
    /// A partially known subject from an enclosing application. Congruence
    /// may read its shape, but solutions and semantic queries must first
    /// discharge this separate scratch world. No cross-call meta escapes.
    pub(super) subject_metas: Option<(u32, &'a [Sol])>,
    pub(super) type_args: &'a dyn Fn(&Term, u32) -> Option<Vec<bool>>,
    pub(super) canonical_head: &'a dyn Fn(&Term, u32) -> Option<Term>,
    /// A rigid subject type re-spelled as a registered declaration's
    /// reference (`El(app(D#tycode_fn; …))`), for a pattern written through
    /// that reference while the subject arrived as the inline lowering — an
    /// equation's endpoint type inferred from a constructor value is the
    /// usual one (issues/instance-binder-occurrence-through-binder-types.md,
    /// issues/elaborator-canonical-type-spelling.md). `None` declines.
    pub(super) respell: &'a dyn Fn(&Type) -> Option<Type>,
    /// A rigid subject type of a generic declaration that registered no code
    /// function, spelled as its **constructor** applied to its type arguments
    /// (`El(app(λ A. ⌜Tac<El A>⌝; ⌜Nat⌝))`,
    /// [`crate::Elaborator::constructor_spelling`]): what [`Self::respell`]
    /// cannot give, asked only by an applied meta's pattern
    /// (issues/higher-kinded-classes.md). `None` declines.
    pub(super) constructor: &'a dyn Fn(&Type) -> Option<Type>,
    /// A re-spelled subject `El(app(D#tycode_fn^δ; ā))` read as the type
    /// constructor at `D`'s declared slot and the argument there
    /// ([`crate::Elaborator::slot_view`],
    /// docs/lambda-carrier-instances-design.md §7.3 reader 2), asked only by
    /// an applied meta of one argument. `None` declines, and the aligned
    /// spine's head-plus-leading-arguments rule applies.
    pub(super) slot_view: &'a dyn Fn(&Term) -> Option<(Term, Term)>,
    /// Every write goes through [`assign`], and this is its one check
    /// (docs/elaborator-principles-survey.md P1,
    /// issues/unifier-checked-assignment.md): may `slot` take the solution,
    /// given what the others hold now? The elaborator's answer holds it to
    /// the slot's declared type ([`crate::Elaborator::solution_fits`]);
    /// `false` leaves the slot open, which learn-only always permits.
    pub(super) admit: &'a dyn Fn(usize, &Term, &[Sol]) -> bool,
    /// Told when a slot already solved meets a subject that is not its
    /// solution, syntactically: the first write won, and this is the later
    /// one it was never compared with. Only told, never acted on: the two
    /// may still convert, and the caller decides whether a refusal it is
    /// about to report is this disagreement's downstream. `None` skips the
    /// comparison (and the strengthening it needs).
    pub(super) disagree: Option<&'a dyn Fn(usize, &Term)>,
    /// A rigid subject term in `gamma` unfolded to its **next head**: the
    /// first transparent reduct whose spine is headed by another global or
    /// local, or is no application at all. What the δ-lazy order compares
    /// next at a rigid head mismatch (docs/elaborator-principles-survey.md
    /// P3, issues/unifier-lazy-delta.md). `None` when the subject does not
    /// unfold, or not within the walk's budget.
    pub(super) next_head: &'a dyn Fn(&Term) -> Option<Term>,
    /// Whether the approximate rules may write now ([`Guesses`]).
    pub(super) guesses: Guesses<'a>,
}

/// What the unifier does at one of its **guesses**: a rule that picks one
/// solution among several the equation allows, rather than the one it
/// forces (docs/elaborator-principles-survey.md P2,
/// issues/unifier-guesses-postponed.md). There are two, both at an unsolved
/// applied meta whose rigid subject spine is **longer** than the pattern's:
/// `?M(Nat) ≟ Pair2<Nat, Bool>` learns `?M := Pair2<Nat>` (the head with its
/// leading arguments, the last argument abstracted), though `λ A ⇒
/// Pair2<A, Bool>` and `λ _ ⇒ Pair2<Nat, Bool>` solve it as well; and
/// `?op(x, y) ≟ append<A>(x, y)` learns the type prefix the same way. The
/// equal-length alignment, a meta at a declared slot ([`slot_pair`]) and
/// every first-order rule are decided, and run in every mode.
#[derive(Clone, Copy)]
pub(crate) enum Guesses<'a> {
    /// Guess where the rule applies, as every caller but an application's
    /// own reads did before guesses were ordered.
    Take,
    /// Do not guess: leave the slot open and set the flag, so the caller can
    /// take the guess **last**, once every forced solution the call has
    /// (its other arguments, the expected type) is in.
    Postpone(&'a Cell<bool>),
    /// Guess, and record the slot guessed, so that a refusal downstream can
    /// name the guess rather than only its consequence.
    Record(&'a RefCell<Vec<usize>>),
}

impl Guesses<'_> {
    /// May the guess at `slot` be taken now?
    fn take(self, slot: usize) -> bool {
        match self {
            Guesses::Take => true,
            Guesses::Postpone(postponed) => {
                postponed.set(true);
                false
            }
            Guesses::Record(guessed) => {
                let mut guessed = guessed.borrow_mut();
                if !guessed.contains(&slot) {
                    guessed.push(slot);
                }
                true
            }
        }
    }
}

/// Is `?M(p̄) ≟ C(ā)`, with `?M` the open slot `slot`, a guess: a subject
/// spine longer than the pattern's, so that `?M` would take `C` with leading
/// arguments the equation does not force ([`Guesses`])?
fn guess_at(head: &Term, n: u32, pat: &Term, subj: &Term, sols: &[Sol]) -> Option<usize> {
    let Term::GlobalTm { var, .. } = head else { return None };
    (var.0 < n && matches!(sols[var.0 as usize], Sol::Unsolved) && spine_len(subj) > spine_len(pat))
        .then_some(var.0 as usize)
}

/// The subject `s`, `d` binders past `gamma`, unfolded to its next head
/// ([`U::next_head`]) and weakened back: the δ-lazy order's one step at a
/// rigid head mismatch. Only the subject unfolds. It is committed-world and
/// closed under `gamma` once strengthened; the pattern mentions this call's
/// metas, which no world here declares. Learning from a reduct of the
/// subject learns what conversion with the subject would: they convert.
fn subject_unfolded(u: &U<'_>, s: &Term, d: u32) -> Option<Term> {
    let s0 = u.subject_tm(s, d)?;
    let w = (u.next_head)(&s0)?;
    let w = match u.subject_metas {
        Some((m, _)) => w.shift_global(m),
        None => w,
    };
    Some(w.apply_local(&embed(u.gamma, d)))
}

/// The unifier's one write. An open slot takes `s` if [`U::admit`] lets
/// it; a solved one is compared with `s` when a caller listens
/// ([`U::disagree`]); a withheld one is never touched.
fn assign(u: &U<'_>, slot: usize, s: Term, sols: &mut [Sol]) {
    match &sols[slot] {
        Sol::Unsolved => {
            if (u.admit)(slot, &s, sols) {
                sols[slot] = Sol::Solved(Rc::new(s));
            }
        }
        Sol::Solved(t) => {
            if let Some(disagree) = u.disagree
                && **t != s
            {
                disagree(slot, &s);
            }
        }
        Sol::Withheld => {}
    }
}

/// Is a write to `slot` worth reading the subject for: open, or solved
/// and compared.
fn writable(u: &U<'_>, slot: usize, sols: &[Sol]) -> bool {
    match &sols[slot] {
        Sol::Unsolved => true,
        Sol::Solved(_) => u.disagree.is_some(),
        Sol::Withheld => false,
    }
}

impl<'a> U<'a> {
    fn subject_ty(&self, t: &Type, d: u32) -> Option<Type> {
        let t = strengthen_ty(self.gamma, t, d)?;
        match self.subject_metas {
            Some((n, sols)) => zonked(&t, n, sols),
            None => Some(t),
        }
    }

    fn subject_tm(&self, t: &Term, d: u32) -> Option<Term> {
        let t = strengthen_tm(self.gamma, t, d)?;
        match self.subject_metas {
            Some((n, sols)) => zonked_tm(&t, n, sols),
            None => Some(t),
        }
    }

    /// Are a pattern spine's head and a subject spine's head two **different
    /// atoms** — distinct locals, distinct committed globals, or one of each?
    /// Neither kind is a meta, so no solution makes them one: the spines are
    /// different applications, and their arguments have nothing to pair. A
    /// pattern's committed global sits `n` above its committed index, and a
    /// partially known subject's `m` above its own; one of the subject's
    /// metas (below `m`) is not an atom. Locals compare at the same depth on
    /// both sides. Anything else (a projection, a λ, a meta) is not decided
    /// here.
    fn distinct_heads(&self, pat: &Term, subj: &Term, n: u32) -> bool {
        let m = self.subject_metas.map_or(0, |(m, _)| m);
        match (pat, subj) {
            (Term::Var(a), Term::Var(b)) => a != b,
            (Term::GlobalTm { var: a, .. }, Term::GlobalTm { var: b, .. }) => {
                a.0 >= n && b.0 >= m && a.0 - n != b.0 - m
            }
            (Term::Var(_), Term::GlobalTm { var, .. }) => var.0 >= m,
            (Term::GlobalTm { var, .. }, Term::Var(_)) => var.0 >= n,
            _ => false,
        }
    }

    /// No head can be read: every `app@` spine is refused by
    /// [`matching_value_spine`], and nothing else changes.
    #[cfg(test)]
    pub(super) fn syntactic(gamma: &'a LocalCtx) -> Self {
        U {
            gamma,
            subject_metas: None,
            type_args: &|_, _| None,
            canonical_head: &|_, _| None,
            respell: &|_| None,
            constructor: &|_| None,
            slot_view: &|_| None,
            admit: &|_, _, _| true,
            disagree: None,
            next_head: &|_| None,
            guesses: Guesses::Take,
        }
    }
}

/// [`unify_ty`] as the elaborator enters it: one bracket per *root* attempt,
/// so the timer measures unification and the recursive congruence below it
/// carries no clock at all (`docs/instrumentation-design.md` §5).
pub(super) fn unify_ty_root(
    u: &U<'_>,
    pat: &Type,
    subj: &Type,
    n: u32,
    d: u32,
    sols: &mut [Sol],
) {
    crate::stats::count(crate::stats::Counter::UnifyCalls);
    crate::stats::timed(crate::stats::Timer::Unify, || unify_ty(u, pat, subj, n, d, sols));
}

pub(super) fn unify_ty(
    u: &U<'_>,
    pat: &Type,
    subj: &Type,
    n: u32,
    d: u32,
    sols: &mut [Sol],
) {
    // The `El` rule. Checked before the congruence so that `El ?A` meeting a
    // *decoded* `El t` still solves rather than descending into the code.
    if let Type::El { tm, .. } = pat
        && let Term::GlobalTm { var, subst } = &**tm
        && var.0 < n
    {
        // The Miller-pattern guard (docs/unifier-completeness-design.md §6):
        // the delayed substitution must be exactly the weakened identity
        // `embed(Γ, d)` — the one condition under which taking the
        // strengthened subject verbatim *is* the pattern inversion. Every
        // reachable renaming today is of this class (established structurally
        // and by an instrumented full run, design §6.1); anything else — a
        // non-variable payload, and the today-unreachable permuted or
        // dropping renamings — is declined, which learn-only always permits.
        if writable(u, var.0 as usize, sols)
            && *subst == embed(u.gamma, d)
            && let Some(s) = u.subject_ty(subj, d)
            && let Some(c) = code::code_of(&s)
        {
            assign(u, var.0 as usize, c, sols);
        }
        return;
    }
    // A subject whose code is a β-redex — the type of an `∃`'s proof read
    // off a call, `El(app(λk. P; witness))` — is read as its contractum,
    // which may itself be a former a pattern `Id`/`Π`/… meets
    // (issues/exists-proof-projection-type-not-reduced.md). Against an `El`
    // pattern the codes meet in `unify_tm`, which contracts both sides.
    let contracted;
    let subj = match subj {
        Type::El { level, tm } if !matches!(pat, Type::El { .. }) => match spelling::beta_head(tm) {
            Some(r) => {
                contracted = Type::El { level: level.clone(), tm: Rc::new(r) };
                &contracted
            }
            None => subj,
        },
        _ => subj,
    };
    // The subject may be `El` of a canonical code rather than the former
    // itself — a record field read off a type that arrived through a
    // `Val -> Type` *value* is exactly that (docs/record-type-values.md §4).
    // `decoded` is the same context-free strip the structural readers of
    // `inductive.rs` use: canonical codes only, never a neutral, so this walk
    // still does no δ. Below the pattern's own `El` rule, which must keep
    // seeing an undecoded subject so `El ?A` solves whole.
    let subj = &*inductive::decoded(subj);
    match (pat, subj) {
        (
            Type::Id {
                ty: t1,
                lhs: a1,
                rhs: b1,
                ..
            },
            Type::Id {
                ty: t2,
                lhs: a2,
                rhs: b2,
                ..
            },
        ) => {
            unify_ty(u, t1, t2, n, d, sols);
            unify_tm(u, a1, a2, n, d, sols);
            unify_tm(u, b1, b2, n, d, sols);
        }
        // `Π`/`Σ`/`W` bind in their second component; `+` does not.
        (
            Type::Pi {
                dom: a1, cod: b1, ..
            },
            Type::Pi {
                dom: a2, cod: b2, ..
            },
        )
        | (
            Type::Sigma {
                fst: a1, snd: b1, ..
            },
            Type::Sigma {
                fst: a2, snd: b2, ..
            },
        )
        | (
            Type::W {
                shape: a1, pos: b1, ..
            },
            Type::W {
                shape: a2, pos: b2, ..
            },
        ) => {
            unify_ty(u, a1, a2, n, d, sols);
            unify_ty(u, b1, b2, n, d + 1, sols);
        }
        (
            Type::Sum {
                lhs: a1, rhs: b1, ..
            },
            Type::Sum {
                lhs: a2, rhs: b2, ..
            },
        ) => {
            unify_ty(u, a1, a2, n, d, sols);
            unify_ty(u, b1, b2, n, d, sols);
        }
        (
            Type::Vec {
                elem: e1, len: k1, ..
            },
            Type::Vec {
                elem: e2, len: k2, ..
            },
        ) => {
            unify_ty(u, e1, e2, n, d, sols);
            unify_tm(u, k1, k2, n, d, sols);
        }
        // A `Wf`'s arity is scoped under its shape binder — the same +1 a `Σ`
        // tail gets, and the reason this is not a flat structural walk.
        (
            Type::Wf {
                shape: s1,
                arity: a1,
                ..
            },
            Type::Wf {
                shape: s2,
                arity: a2,
                ..
            },
        ) => {
            unify_ty(u, s1, s2, n, d, sols);
            unify_tm(u, a1, a2, n, d + 1, sols);
        }
        (Type::Fin { len: k1 }, Type::Fin { len: k2 }) => {
            unify_tm(u, k1, k2, n, d, sols);
        }
        // A codata instance `M(I; S; P; next)(j)`: the shape binds the index,
        // the positions index and shape, `next` all three
        // (docs/codata-elaborator-design.md §2) — so a type argument read off
        // a constructor's field is learned under those binders.
        (Type::M { sig: g1, index: j1 }, Type::M { sig: g2, index: j2 }) => {
            if !Rc::ptr_eq(g1, g2) {
                unify_ty(u, &g1.idx, &g2.idx, n, d, sols);
                unify_ty(u, &g1.shape, &g2.shape, n, d + 1, sols);
                unify_ty(u, &g1.pos, &g2.pos, n, d + 2, sols);
                unify_tm(u, &g1.next, &g2.next, n, d + 3, sols);
            }
            unify_tm(u, j1, j2, n, d, sols);
        }
        // An `IWf`-route family instance (docs/iwf-former-design.md §8): the
        // arity and output index are scoped under the shape binder, the child
        // index under it and the position. A type argument is learned from
        // the shape, where its stored fields mention it.
        (Type::IWf { sig: g1, index: j1 }, Type::IWf { sig: g2, index: j2 }) => {
            if !Rc::ptr_eq(g1, g2) {
                unify_ty(u, &g1.idx, &g2.idx, n, d, sols);
                unify_ty(u, &g1.shape, &g2.shape, n, d, sols);
                unify_tm(u, &g1.arity, &g2.arity, n, d + 1, sols);
                unify_tm(u, &g1.out, &g2.out, n, d + 1, sols);
                unify_tm(u, &g1.child, &g2.child, n, d + 2, sols);
            }
            unify_tm(u, j1, j2, n, d, sols);
        }
        (
            Type::DVec {
                len: k1, fam: f1, ..
            },
            Type::DVec {
                len: k2, fam: f2, ..
            },
        ) => {
            unify_tm(u, k1, k2, n, d, sols);
            unify_ty(u, f1, f2, n, d + 1, sols);
        }
        (Type::El { tm: t1, .. }, Type::El { tm: t2, .. }) => {
            unify_tm(u, t1, t2, n, d, sols);
        }
        // A pattern spelled through a declaration's code, `El(app(D#code;
        // ?A))`, against the inline lowering of the same declaration: the
        // two spellings share nothing structural to align. Re-spell the
        // subject as the reference the pattern uses and align those. Only
        // while the pattern still has something to learn — its code mentions
        // an unsolved meta — and only for a committed code at the head, never
        // a flex one. Scoped like the term reduction: strengthened to
        // `gamma`, re-spelled there, weakened back.
        (Type::El { tm, .. }, s)
            if !matches!(s, Type::El { .. })
                && (committed_head(tm, n) || flex_applied_head(tm, n))
                && zonked_tm(tm, n, sols).is_none() =>
        {
            let flex = !committed_head(tm, n);
            let Some(s0) = u.subject_ty(s, d) else { return };
            let respelled = (u.respell)(&s0);
            if respelled.is_none()
                && flex
                && let Some(Type::El { tm: c, .. }) = (u.constructor)(&s0)
            {
                let c = match u.subject_metas {
                    Some((m, _)) => c.shift_global(m),
                    None => (*c).clone(),
                };
                flex_spine(u, tm, &c.apply_local(&embed(u.gamma, d)), n, d, sols);
                return;
            }
            // `?M(p)` against a declaration with a declared slot: `?M` is the
            // constructor at that slot and `p` its argument there, rather than
            // the head with the leading arguments.
            if flex
                && let Some(Type::El { tm: r, .. }) = &respelled
                && slot_pair(u, tm, r, n, d, sols)
            {
                return;
            }
            if let Some(r @ Type::El { .. }) = respelled {
                let r = match u.subject_metas {
                    Some((m, _)) => r.shift_global(m),
                    None => r,
                };
                unify_ty(u, pat, &r.apply_local(&embed(u.gamma, d)), n, d, sols);
            }
        }
        // A former against `El` of a code a definition computes: the
        // δ-lazy order's step at the type level. The subject's code unfolds
        // to its next head, and the decoded result meets the pattern again
        // (issues/unifier-lazy-delta.md) — a hypothesis `Lt(x, y)` against a
        // domain spelled as the `Id` or `Π` its definition is.
        (p, Type::El { level, tm })
            if !matches!(p, Type::El { .. } | Type::Ty(_)) && reducible(tm) && zonked(pat, n, sols).is_none() =>
        {
            if let Some(r) = subject_unfolded(u, tm, d) {
                let unfolded = Type::El { level: level.clone(), tm: Rc::new(r) };
                unify_ty(u, pat, &unfolded, n, d, sols);
            }
        }
        // `Nat`/`Unit`/`Empty`/`Ty` and every mismatched pairing: nothing to
        // learn. A mismatch is not an error here — this function only ever
        // learns, and the kernel is what decides whether the call typechecks.
        _ => {}
    }
}

/// Term-level companion of [`unify_ty`]. When `pat` is an unsolved
/// metavariable under the weakened identity renaming `embed(Γ, d)` (the
/// Miller pattern condition, in the one class reachable today — design §6),
/// record the strengthened subject; otherwise recurse through matching heads
/// toward nested metas. For an occurrence `?m^{embed(Γ,d)}` and a subject `s`
/// with `strengthen_tm(Γ, s, d) = Some(s₀)`, the recorded `?m := s₀`
/// satisfies `s₀[embed(Γ,d)] = s₀.shift(d) = s` — the verbatim take plus the
/// strengthening that already runs *is* the inversion for this class.
/// How many arguments a spine applies. Used by the value-spine rule.
fn spine_len(mut t: &Term) -> usize {
    let mut k = 0;
    while let Some((fun, _)) = spelling::app_of(t) {
        k += 1;
        t = fun;
    }
    k
}

/// The subject is in the committed world, so even global index zero is
/// rigid: only the pattern uses indices below `n` as scratch metas. A field
/// read off a rigid receiver is as rigid as the receiver: a class
/// dictionary's `K.inv(x)` is `fst@(snd@(…(d)))(x)`, which a morphism's
/// `?neg_b(map(x))` learns `?neg_b := K.inv` from
/// (issues/cast-reading-through-local-morphism.md).
fn rigid_head(mut t: &Term) -> bool {
    while let Some((fun, _)) = spelling::app_of(t) {
        t = fun;
    }
    while let Some((_, receiver)) = projection_of(t) {
        t = receiver;
    }
    matches!(t, Term::Var(_) | Term::GlobalTm { .. })
}

/// A pattern spine head that cannot be solved: a local, or a committed
/// global (index `n` or above in the scratch world).
fn rigid_atom(head: &Term, n: u32) -> bool {
    match head {
        Term::Var(_) => true,
        Term::GlobalTm { var, .. } => var.0 >= n,
        _ => false,
    }
}

/// Align value arguments, allowing only a leading type-argument prefix on
/// the rigid side: `?op(x, y)` can learn `append<A>`, but `?f(x)` must not
/// learn `add(a)` from `add(a, x)`.
fn matching_value_spine(u: &U<'_>, pat: &Term, subj: &Term, d: u32) -> bool {
    let committed;
    let mut subj = if let Some((n, sols)) = u.subject_metas {
        let Some(t) = zonked_tm(subj, n, sols) else { return false; };
        committed = t;
        &committed
    } else { subj };
    if !rigid_head(subj) {
        return false;
    }
    for _ in 0..spine_len(pat) {
        let Some((fun, _)) = spelling::app_of(subj) else {
            return false;
        };
        subj = fun;
    }
    // The remaining prefix must be type arguments. An `app` node states its
    // domain; an `app@` node's is its head's, read once for the whole
    // prefix only when one is present.
    let mut heads: Option<Vec<bool>> = None;
    let mut k = spine_len(subj);
    while let Some((fun, _)) = spelling::app_of(subj) {
        k -= 1;
        let is_ty = match subj {
            Term::App { dom, .. } => matches!(&**dom, Type::Ty(_)),
            _ => {
                if heads.is_none() {
                    heads = (u.type_args)(subj, d);
                }
                match heads.as_ref().and_then(|h| h.get(k)) {
                    Some(t) => *t,
                    None => return false,
                }
            }
        };
        if !is_ty {
            return false;
        }
        subj = fun;
    }
    true
}

fn unify_tm(u: &U<'_>, pat: &Term, subj: &Term, n: u32, d: u32, sols: &mut [Sol]) {
    if let Term::GlobalTm { var, subst } = pat
        && var.0 < n
    {
        if writable(u, var.0 as usize, sols)
            && *subst == embed(u.gamma, d)
            && let Some(s) = u.subject_tm(subj, d)
        {
            assign(u, var.0 as usize, s, sols);
        }
        return;
    }
    // A side headed by a β-redex has nothing to align until it contracts:
    // the application congruence would pair the other side's spine against
    // the λ and its argument, and teach the pattern's last argument the
    // redex's (issues/exists-proof-projection-type-not-reduced.md). Both
    // sides contract, since a pattern carries redexes too — a record field
    // `protected(register)` instantiated at `λ r => Kept(?scratch, r)` — and
    // one contracted against one not would stop meeting. Contracting head
    // λs is syntactic and needs no context, so it runs before any other
    // rule, on every pairing; a well-typed term's head redexes run out.
    let (p, s) = (spelling::beta_head(pat), spelling::beta_head(subj));
    if p.is_some() || s.is_some() {
        let pat = p.as_ref().unwrap_or(pat);
        let subj = s.as_ref().unwrap_or(subj);
        return unify_tm(u, pat, subj, n, d, sols);
    }
    match (pat, subj) {
        (Term::Succ(a), Term::Succ(b)) => unify_tm(u, a, b, n, d, sols),
        // A numeral is `Succ^k(Zero)` (kernel `NatLit`), so `Succ(?n) ≟ 8`
        // learns `?n := 7` — the width a method on `BitVec(Succ(n))` needs
        // at a literal-width receiver. Learn-only, like every case here.
        (Term::Succ(a), Term::NatLit(k)) if !k.is_zero() => {
            unify_tm(u, a, &heather_kernel::term::nat_lit_pred(k), n, d, sols)
        }
        (Term::NatLit(k), Term::Succ(b)) if !k.is_zero() => {
            unify_tm(u, &heather_kernel::term::nat_lit_pred(k), b, n, d, sols)
        }
        // Either spelling on either side: `app` and `app@` are one former
        // (`docs/app-by-head-type-design.md` §6.2), and this congruence
        // never read the annotations.
        (p, s) if spelling::is_app(p) && spelling::is_app(s) => {
            let (f1, a1) = spelling::app_of(p).expect("an application");
            let (f2, a2) = spelling::app_of(s).expect("an application");
            // The flex-head guard (design §5.4): a pattern application whose
            // spine head is one of this call's not-yet-solved metas learns
            // nothing here. The `App` congruence would otherwise "solve"
            // `?f(?a) ≟ add(a, a)` by peeling one argument — `?f := add(a)` —
            // satisfying this occurrence and contradicting the next. Flex
            // heads applied to arbitrary terms are outside the Miller
            // fragment. Except for the aligned rigid spine below, they are
            // left to the LGG hook ([`Elaborator::solve_from_expected`]);
            // this guard keeps partial-value guessing out. In the pattern,
            // committed globals sit at `var.0 >= n`, so `D#fam` family spines
            // (the type-arg-inference-through-index walker) are untouched.
            let mut head = pat;
            while let Some((fun, _)) = spelling::app_of(head) {
                head = fun;
            }
            // A head meta already solved to a λ — a constructor at a
            // declared slot, `λ A. Result<A, E>` — is substituted and the
            // redex contracted first: paired positionally, `?M(?B) ≟
            // Result<Nat, Bool>` would teach `?B := Bool`, the argument the
            // λ fixes (docs/lambda-carrier-instances-design.md §7.3).
            if let Term::GlobalTm { var, .. } = head
                && var.0 < n
                && sols[var.0 as usize].solved().is_some_and(|t| matches!(&**t, Term::Lam { .. }))
            {
                let p2 = partially_zonked_tm(pat, n, sols, u.gamma);
                if let Some(r) = spelling::beta_head(&p2) {
                    return unify_tm(u, &r, subj, n, d, sols);
                }
            }
            // `?M(p)` against a declaration's code spine with a declared
            // slot: the constructor at that slot, not the aligned spine's
            // head plus leading arguments
            // (docs/lambda-carrier-instances-design.md §7.3 reader 2).
            if let Term::GlobalTm { var, .. } = head
                && var.0 < n
                && sols[var.0 as usize].solved().is_none()
                && spine_len(pat) == 1
                && matches!(spine_head(s), Term::GlobalTm { .. })
                && let Some(s0) = u.subject_tm(s, d)
                && slot_pair(u, pat, &s0, n, d, sols)
            {
                return;
            }
            //
            // Align the value spine against a rigid global or local head.
            // A leading type-only prefix may specialize a polymorphic
            // declaration: `?op(x, y)` learns `append<A>`. Extra value
            // arguments remain refused (`?f(x)` cannot learn `add(a)`).
            // This is structural, learn-only inference, not higher-order
            // search; the completed application still passes the kernel.
            if let Term::GlobalTm { var, .. } = head
                && var.0 < n
                && sols[var.0 as usize].solved().is_none()
                && !matching_value_spine(u, pat, subj, d)
            {
                return;
            }
            // The aligned spine is a guess when the subject's is longer: the
            // leading arguments `?M` takes are one choice among several
            // ([`Guesses`]), so it waits while the caller postpones guesses.
            if let Some(slot) = guess_at(head, n, pat, subj, sols)
                && !u.guesses.take(slot)
            {
                return;
            }
            // Two rigid spines of different lengths are never the same
            // application, so their arguments have nothing to pair: aligned
            // from the right, they pair a predicate's class indices with
            // whatever sits at the other's positions — `AbsLt(?A, ?≈, ?<,
            // ?≤, ?+, ?d, x, e)` against `-e < x ∧ x < e` taught `?+ :=
            // Rat::Lt`, and against `Close(x, y, e)`, every index one place
            // over (issues/constrained-predicate-expected-type.md). Nor are
            // two rigid spines with different heads, at any length:
            // `Has2(B(lo, hi), ?x)` against `And<Nat, Nat>` paired the
            // predicate's argument with the conjunction's second type and
            // taught `?x := ⌜Nat⌝`, which the expected type would have
            // solved as `x`
            // (issues/and-at-match-predicate-implicit-level-mismatch.md).
            //
            // Either side may still unfold to the other, and that is the
            // δ-lazy order's step, as in the kernel's conversion: a subject
            // headed by a global unfolds to its next head and is compared
            // again (issues/unifier-lazy-delta.md). `Bool::and(?a, ?b)`
            // against `g(n, m)`, where `g`'s body is `n.leb(m) && !m.leb(n)`,
            // learns `?a := n.leb(m)` rather than nothing
            // (issues/unifier-spine-across-distinct-heads.md).
            let mismatch = (rigid_atom(head, n) && rigid_head(s) && spine_len(p) != spine_len(s))
                || u.distinct_heads(head, spine_head(s), n);
            if mismatch {
                unify_unfolded(u, pat, s, n, d, sols);
                return;
            }
            unify_tm(u, f1, f2, n, d, sols);
            unify_tm(u, a1, a2, n, d, sols);
        }
        // Constructor values (issues/unify-through-constructor-values.md). An
        // inductive's constructor is a `supf`/`sup` node whose label is an
        // injection chain into a pair tower of its fields, with its children
        // a pair tower (Wf) or a λ over positions (W). A congruence lemma's
        // implicits sit inside those — `Cons(?l, ?lt)` — so without these
        // cases the goal that states them teaches nothing. Pairs and
        // injections come in two spellings (`pair` and the checked `pair@`,
        // docs/intro-by-type-design.md), either on either side, and like
        // `app`/`app@` above the congruence never reads their annotations.
        (
            Term::Supf { label: l1, children: c1, .. },
            Term::Supf { label: l2, children: c2, .. },
        )
        | (
            Term::Sup { label: l1, children: c1, .. },
            Term::Sup { label: l2, children: c2, .. },
        ) => {
            unify_tm(u, l1, l2, n, d, sols);
            unify_tm(u, c1, c2, n, d, sols);
        }
        (p, s) if pair_of(p).is_some() && pair_of(s).is_some() => {
            let (a1, b1) = pair_of(p).expect("a pair");
            let (a2, b2) = pair_of(s).expect("a pair");
            unify_tm(u, a1, a2, n, d, sols);
            unify_tm(u, b1, b2, n, d, sols);
        }
        (p, s) if injection_of(p).is_some() && injection_of(s).is_some() => {
            let (left1, v1) = injection_of(p).expect("an injection");
            let (left2, v2) = injection_of(s).expect("an injection");
            if left1 == left2 {
                unify_tm(u, v1, v2, n, d, sols);
            }
        }
        // Projections, in either spelling on either side. A record type
        // lowers inline to its fields' Σ tower, so a parameter the fields
        // read through a projection reaches the unifier as `fst@(snd@(?x))`
        // against `fst@(snd@(x))` — `U(x)` with `ok: x.k = v`
        // (issues/implicit-from-record-parameter-type.md). Same component on
        // both sides pairs the receivers. A projection is not injective, so
        // `?x := x` is one solution, not the only one: learn-only, like the
        // application congruence above, and the kernel judges the call.
        (p, s) if projection_of(p).is_some() && projection_of(s).is_some() => {
            let (first1, r1) = projection_of(p).expect("a projection");
            let (first2, r2) = projection_of(s).expect("a projection");
            if first1 == first2 {
                unify_tm(u, r1, r2, n, d, sols);
            }
        }
        (Term::Lam { body: b1, .. }, Term::Lam { body: b2, .. }) => {
            unify_tm(u, b1, b2, n, d + 1, sols);
        }
        // A canonical pattern against a subject that has to compute before
        // it is one: `BitVec(Succ(?n))` at `x: BitVec(m + Succ(k))`, or
        // `Cons(?r, ?rt)` at `rr_bytes(…)`. The subject is committed-world
        // and rigid, so its reduct is the same term; learn from that, and
        // from nothing else. A record's field sits under its lowering's Σ
        // binders, so the subject is strengthened to `gamma` (a solution has
        // to be anyway), reduced there, and weakened back — `embed(Γ, d)` is
        // that weakening. Only a global head can unfold; a variable's never
        // does, so it is not asked.
        (p, s) if canonical_pattern(p) && !canonical(s) && global_head(s) => {
            if let Some(s0) = u.subject_tm(s, d)
                && let Some(w) = (u.canonical_head)(&s0, 0)
            {
                let w = match u.subject_metas {
                    Some((m, _)) => w.shift_global(m),
                    None => w,
                };
                unify_tm(u, pat, &w.apply_local(&embed(u.gamma, d)), n, d, sols);
            }
        }
        // A declared-index family's type is `El` of an **index recursion
        // choosing among quoted codes** — `elimN(M; z «Σ…+…»; s «…»; i)`
        // with the payload type a variable *inside* the code literals
        // (docs/inductive-indexed-lowering.md), so learning `A` from
        // `t: W3<A>(n)` means walking the eliminator and the code
        // constructors (issues/type-arg-inference-through-index.md). Same
        // license as every case here: learn-only, kernel judges. Depths are
        // each variant's own binding structure — motive and Π/Σ/W second
        // components bind one, a step binds two, `Wf`'s arity binds one,
        // `Vec`/`Fin`/`Id`/`sEq`/`+` bind nothing.
        (
            Term::ElimNat {
                motive: m1,
                base: b1,
                step: s1,
                scrut: t1,
                ..
            },
            Term::ElimNat {
                motive: m2,
                base: b2,
                step: s2,
                scrut: t2,
                ..
            },
        ) => {
            unify_ty(u, m1, m2, n, d + 1, sols);
            unify_tm(u, b1, b2, n, d, sols);
            unify_tm(u, s1, s2, n, d + 2, sols);
            unify_tm(u, t1, t2, n, d, sols);
        }
        (
            Term::TmPi {
                dom: a1, cod: b1, ..
            },
            Term::TmPi {
                dom: a2, cod: b2, ..
            },
        )
        | (
            Term::TmSigma {
                fst: a1, snd: b1, ..
            },
            Term::TmSigma {
                fst: a2, snd: b2, ..
            },
        )
        | (
            Term::TmW {
                shape: a1, pos: b1, ..
            },
            Term::TmW {
                shape: a2, pos: b2, ..
            },
        )
        | (
            Term::TmWf {
                shape: a1,
                arity: b1,
                ..
            },
            Term::TmWf {
                shape: a2,
                arity: b2,
                ..
            },
        ) => {
            unify_tm(u, a1, a2, n, d, sols);
            unify_tm(u, b1, b2, n, d + 1, sols);
        }
        (Term::TmDVec { len: k1, fam: f1, .. }, Term::TmDVec { len: k2, fam: f2, .. }) => {
            unify_tm(u, k1, k2, n, d, sols);
            unify_tm(u, f1, f2, n, d + 1, sols);
        }
        (
            Term::TmIWf { idx: x1, shape: s1, arity: a1, out: o1, child: c1, index: m1, .. },
            Term::TmIWf { idx: x2, shape: s2, arity: a2, out: o2, child: c2, index: m2, .. },
        ) => {
            unify_tm(u, x1, x2, n, d, sols);
            unify_tm(u, s1, s2, n, d, sols);
            unify_tm(u, a1, a2, n, d + 1, sols);
            unify_tm(u, o1, o2, n, d + 1, sols);
            unify_tm(u, c1, c2, n, d + 2, sols);
            unify_tm(u, m1, m2, n, d, sols);
        }
        (
            Term::TmM { idx: x1, shape: s1, pos: p1, next: o1, index: j1, .. },
            Term::TmM { idx: x2, shape: s2, pos: p2, next: o2, index: j2, .. },
        ) => {
            unify_tm(u, x1, x2, n, d, sols);
            unify_tm(u, s1, s2, n, d + 1, sols);
            unify_tm(u, p1, p2, n, d + 2, sols);
            unify_tm(u, o1, o2, n, d + 3, sols);
            unify_tm(u, j1, j2, n, d, sols);
        }
        (
            Term::TmSum {
                lhs: a1, rhs: b1, ..
            },
            Term::TmSum {
                lhs: a2, rhs: b2, ..
            },
        ) => {
            unify_tm(u, a1, a2, n, d, sols);
            unify_tm(u, b1, b2, n, d, sols);
        }
        (
            Term::TmVec {
                elem: e1, len: k1, ..
            },
            Term::TmVec {
                elem: e2, len: k2, ..
            },
        ) => {
            unify_tm(u, e1, e2, n, d, sols);
            unify_tm(u, k1, k2, n, d, sols);
        }
        (Term::TmFin { len: k1 }, Term::TmFin { len: k2 }) => {
            unify_tm(u, k1, k2, n, d, sols);
        }
        (
            Term::TmId {
                ty: t1,
                lhs: a1,
                rhs: b1,
                ..
            },
            Term::TmId {
                ty: t2,
                lhs: a2,
                rhs: b2,
                ..
            },
        )
        | (
            Term::TmSEq {
                ty: t1,
                lhs: a1,
                rhs: b1,
                ..
            },
            Term::TmSEq {
                ty: t2,
                lhs: a2,
                rhs: b2,
                ..
            },
        ) => {
            unify_tm(u, t1, t2, n, d, sols);
            unify_tm(u, a1, a2, n, d, sols);
            unify_tm(u, b1, b2, n, d, sols);
        }
        // Any other pairing: the two do not meet as they stand, and the
        // subject may still compute to something that does — a field type
        // read through a projection, `fst(⟨λ b => BitVec(64), …⟩)`, or a
        // definition's body. The δ-lazy order's step, as at a head mismatch.
        _ => unify_unfolded(u, pat, subj, n, d, sols),
    }
}

/// The δ-lazy order's step (issues/unifier-lazy-delta.md): when `pat` and
/// `subj` do not meet as they stand, unfold the subject to its next head
/// ([`U::next_head`]) and compare again. Only while the pattern still has an
/// open slot to learn — otherwise there is nothing to read, and at a closed
/// verdict the unfolding is the verdict's whole evaluation
/// (issues/closed-verdict-evaluated-twice.md) — and only a subject that can
/// step: one headed by a global, a β-redex or an eliminator. Each hop is a
/// strict reduct, so the chain ends where the subject stops reducing.
fn unify_unfolded(u: &U<'_>, pat: &Term, subj: &Term, n: u32, d: u32, sols: &mut [Sol]) {
    if !reducible(subj) || zonked_tm(pat, n, sols).is_some() {
        return;
    }
    if let Some(r) = subject_unfolded(u, subj, d) {
        unify_tm(u, pat, &r, n, d, sols);
    }
}

/// Can `t` take a head step: its spine is headed by a global (δ), a λ (β)
/// or an eliminator (ι, once its scrutinee is a constructor)?
fn reducible(t: &Term) -> bool {
    let h = spine_head(t);
    matches!(h, Term::GlobalTm { .. }) || steps_through(h)
}

/// A spine head a walk to the next head keeps stepping through: a λ (the
/// spine is a β-redex) or an eliminator, which reduces once its scrutinee
/// is a constructor and is no head a pattern could meet before then.
pub(crate) fn steps_through(h: &Term) -> bool {
    matches!(
        h,
        Term::Lam { .. }
            | Term::ElimNat { .. }
            | Term::J { .. }
            | Term::ElimSEmpty { .. }
            | Term::ElimSquash { .. }
            | Term::ElimEmpty { .. }
            | Term::Fst { .. }
            | Term::Snd { .. }
            | Term::FstAt { .. }
            | Term::SndAt { .. }
            | Term::Case { .. }
            | Term::ElimW { .. }
            | Term::ElimWf { .. }
            | Term::ElimIWf { .. }
            | Term::Out { .. }
            | Term::ElimCodeTy { .. }
            | Term::ElimCodeTm { .. }
    )
}

/// A form [`U::canonical_head`] can reduce a subject to.
pub(super) fn canonical(t: &Term) -> bool {
    matches!(t, Term::Succ(_) | Term::NatLit(_)) || canonical_pattern(t)
}

/// A pattern whose congruence a reduced subject could feed: every canonical
/// form but a numeral, which has no metavariable to learn.
fn canonical_pattern(t: &Term) -> bool {
    matches!(t, Term::Succ(_) | Term::Supf { .. } | Term::Sup { .. })
        || pair_of(t).is_some()
        || injection_of(t).is_some()
}

/// Is the spine's head a **committed** global — in the pattern's scratch
/// world, one at index `n` or above, never a metavariable?
fn committed_head(mut t: &Term, n: u32) -> bool {
    while let Some((fun, _)) = spelling::app_of(t) {
        t = fun;
    }
    matches!(t, Term::GlobalTm { var, .. } if var.0 >= n)
}

/// Is `t` a meta of this call **applied** to at least one argument —
/// `?M(⌜Nat⌝)`, the type `M(Nat)` of a parameter over a type constructor
/// `M: Type → Type` (issues/higher-kinded-classes.md, piece 1)? Its subject
/// is re-spelled through the declaration's code like a committed head's, so
/// `El(app(?M; ⌜Nat⌝))` meets `El(app(Option#tycode_fn^δ; ⌜Nat⌝))` and the
/// application congruence's aligned-spine rule takes the first-order
/// solution `?M := Option#tycode_fn^δ` (head plus leading type arguments,
/// the last one abstracted — Lean's and Haskell's approximation).
fn flex_applied_head(mut t: &Term, n: u32) -> bool {
    let mut applied = false;
    while let Some((fun, _)) = spelling::app_of(t) {
        applied = true;
        t = fun;
    }
    applied && matches!(t, Term::GlobalTm { var, .. } if var.0 < n)
}

/// An applied meta `?M(p̄)` against a rigid application `C(ā)` whose head
/// is a **λ** — [`U::constructor`]'s spelling of a type with no registered
/// code function. The application congruence cannot take this pair, because
/// it contracts a β-redex head before anything else and the λ would vanish
/// into its body; so the first-order rule is applied here directly: `?M`
/// takes `C` with the leading arguments, and the last `|p̄|` arguments pair
/// with the pattern's. Learn-only, like every rule here.
fn flex_spine(u: &U<'_>, pat: &Term, subj: &Term, n: u32, d: u32, sols: &mut [Sol]) {
    let mut pargs = Vec::new();
    let mut head = pat;
    while let Some((fun, arg)) = spelling::app_of(head) {
        pargs.push(arg);
        head = fun;
    }
    // A longer subject spine is the head-with-leading-arguments guess
    // ([`Guesses`]); an equal one pairs the λ with `?M` as it stands.
    if let Some(slot) = guess_at(head, n, pat, subj, sols)
        && !u.guesses.take(slot)
    {
        return;
    }
    let mut sargs = Vec::new();
    let mut prefix = subj;
    for _ in 0..pargs.len() {
        let Some((fun, arg)) = spelling::app_of(prefix) else {
            return;
        };
        sargs.push(arg);
        prefix = fun;
    }
    unify_tm(u, head, prefix, n, d, sols);
    for (p, a) in pargs.into_iter().zip(sargs) {
        unify_tm(u, p, a, n, d, sols);
    }
}

/// `?M(p) ≟ D<ā>` at `D`'s declared slot `s`: learn `?M` as the constructor
/// at `s` and pair `p` with `a_s` ([`U::slot_view`]). `subj` is the subject's
/// code spine already strengthened to `gamma` (and, under
/// [`U::subject_metas`], in the committed world), as [`U::subject_tm`] and the
/// re-spelling arm hand it over. `false`, learning nothing, when the pattern
/// is not a meta applied to one argument or `D` declares no slot.
fn slot_pair(u: &U<'_>, pat: &Term, subj: &Term, n: u32, d: u32, sols: &mut [Sol]) -> bool {
    let Some((pfun, parg)) = spelling::app_of(pat) else { return false };
    if !matches!(&**pfun, Term::GlobalTm { var, .. } if var.0 < n) {
        return false;
    }
    let Some((c, a)) = (u.slot_view)(subj) else { return false };
    let lift = |t: Term| {
        let t = match u.subject_metas {
            Some((m, _)) => t.shift_global(m),
            None => t,
        };
        t.apply_local(&embed(u.gamma, d))
    };
    unify_tm(u, pfun, &lift(c), n, d, sols);
    unify_tm(u, parg, &lift(a), n, d, sols);
    true
}

/// The head of an application spine (`t` itself when it is no application).
fn spine_head(mut t: &Term) -> &Term {
    while let Some((fun, _)) = spelling::app_of(t) {
        t = fun;
    }
    t
}

/// Is the spine's head a global, the one head δ can unfold?
fn global_head(mut t: &Term) -> bool {
    while let Some((fun, _)) = spelling::app_of(t) {
        t = fun;
    }
    matches!(t, Term::GlobalTm { .. })
}

/// An application whose head is a global: a declaration applied, as an
/// argument's type is before δ has contracted it into its body.
pub(crate) fn global_spine(t: &Term) -> bool {
    spelling::is_app(t) && global_head(t)
}

/// The two components of a pair in either spelling.
fn pair_of(t: &Term) -> Option<(&Term, &Term)> {
    match t {
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => Some((fst, snd)),
        _ => None,
    }
}

/// Which component a projection takes (`true` for `fst`), and its
/// receiver, in either spelling.
fn projection_of(t: &Term) -> Option<(bool, &Term)> {
    match t {
        Term::Fst { pair, .. } | Term::FstAt { pair } => Some((true, pair)),
        Term::Snd { pair, .. } | Term::SndAt { pair } => Some((false, pair)),
        _ => None,
    }
}

/// Which side an injection takes (`true` for `inl`), and its payload, in
/// either spelling.
fn injection_of(t: &Term) -> Option<(bool, &Term)> {
    match t {
        Term::Inl { val, .. } | Term::InlAt { val, .. } => Some((true, val)),
        Term::Inr { val, .. } | Term::InrAt { val, .. } => Some((false, val)),
        _ => None,
    }
}

/// A parameter domain with the meta block substituted away — `Some` exactly
/// when every metavariable it mentions is already solved, in which case the
/// result is scoped in the *real* Ψ (a `GlobalSubst` over the `n` metas also
/// renumbers the committed globals back down, as `strengthen_global` records).
///
/// "Mentions no unsolved meta" is decided by substituting **two different**
/// markers for the unsolved ones and comparing: an unsolved occurrence makes
/// the two results differ, and nothing else can. Same device as
/// [`strengthen_tm`] — an exact test that needs no traversal of `Term`/`Type`
/// and so cannot drift out of sync with the syntax.
pub(super) fn zonked(dom: &Type, n: u32, sols: &[Sol]) -> Option<Type> {
    let with = |marker: Term| {
        let entries = (0..n)
            .map(|k| {
                GlobalEntry::Tm(match sols[(n - 1 - k) as usize].solved() {
                    Some(t) => Rc::clone(t),
                    // `Unsolved` and `Withheld` alike: a withheld slot must
                    // keep *blocking* — a deferred argument's occurrences in a
                    // dependent domain are exactly what its retry waits on.
                    None => Rc::new(marker.clone()),
                })
            })
            .collect();
        dom.apply_global(&GlobalSubst { entries })
    };
    let a = with(Term::Zero);
    (a == with(Term::Succ(Rc::new(Term::Zero)))).then_some(a)
}

/// Substitute known solutions while keeping unresolved slots in their
/// original scratch world. This exposes a solved domain's structure to a
/// partial-subject harvest without disguising its remaining blockers.
pub(super) fn partially_zonked(dom: &Type, n: u32, sols: &[Sol], gamma: &LocalCtx) -> Type {
    let entries = (0..n).rev().map(|slot| GlobalEntry::Tm(Rc::new(
        match sols[slot as usize].solved() {
            Some(t) => t.shift_global(n),
            None => Term::GlobalTm { var: heather_kernel::term::GlobalVar(slot), subst: LocalSubst::id(gamma) },
        }
    ))).collect();
    // The substitution consumes n slots, so first weaken the identity region
    // by n. Its payloads already live in the retained scratch world.
    dom.shift_global_above(n, n).apply_global(&GlobalSubst { entries })
}

/// [`partially_zonked`] for a term: solved slots substituted, unsolved ones
/// kept in the scratch world.
fn partially_zonked_tm(t: &Term, n: u32, sols: &[Sol], gamma: &LocalCtx) -> Term {
    let entries = (0..n).rev().map(|slot| GlobalEntry::Tm(Rc::new(
        match sols[slot as usize].solved() {
            Some(t) => t.shift_global(n),
            None => Term::GlobalTm { var: heather_kernel::term::GlobalVar(slot), subst: LocalSubst::id(gamma) },
        }
    ))).collect();
    t.shift_global_above(n, n).apply_global(&GlobalSubst { entries })
}

/// [`zonked`] for a *term* — same two-marker test, same guarantee: `Some`
/// exactly when every metavariable the term mentions is already solved, in
/// which case the result is scoped in the committed Ψ. Used by the congruence
/// rule, whose witnesses are compared with `==` and so must be real terms.
pub(crate) fn zonked_tm(t: &Term, n: u32, sols: &[Sol]) -> Option<Term> {
    let with = |marker: Term| {
        let entries = (0..n)
            .map(|k| {
                GlobalEntry::Tm(match sols[(n - 1 - k) as usize].solved() {
                    Some(t) => Rc::clone(t),
                    None => Rc::new(marker.clone()),
                })
            })
            .collect();
        t.apply_global(&GlobalSubst { entries })
    };
    let a = with(Term::Zero);
    (a == with(Term::Succ(Rc::new(Term::Zero)))).then_some(a)
}

/// The substitution that drops the innermost `d` binders off `gamma`,
/// sending each to a marker. Used only by [`strengthen_ty`]/[`strengthen_tm`].
///
/// `terms` is indexed outermost-first over the *source* context `Γ, d`
/// (length `m + d`), so entry `k` is the image of `Var(m + d - 1 - k)`: the
/// first `m` are `Γ`'s own variables lowered by `d`, and the last `d` are the
/// binders being dropped.
fn drop_binders(gamma: &LocalCtx, d: u32) -> LocalSubst {
    let m = gamma.entries.len() as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty {
            len: m,
            base: CtxBase::Nil,
        },
        CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
    };
    let terms = (0..m)
        .map(|k| Rc::new(Term::Var(LocalVar(m - 1 - k))))
        .chain((0..d).map(|_| Rc::new(Term::Zero)))
        .collect();
    LocalSubst { tail, terms }
}

/// Is `t`, scoped in `Γ` plus `d` further binders, in fact scoped in `Γ`
/// alone — and if so, what is it there?
///
/// Drop the `d` binders to a marker, then shift back by `d` and compare. A
/// term that never mentioned them is restored exactly; one that did keeps a
/// marker where a variable was, and the comparison fails. That is the whole
/// test: no new traversal of `Term`/`Type` is needed, and it cannot drift out
/// of sync with the syntax the way a hand-written occurrence check would.
pub(crate) fn strengthen_tm(gamma: &LocalCtx, t: &Term, d: u32) -> Option<Term> {
    if d == 0 {
        return Some(t.clone());
    }
    let s = t.apply_local(&drop_binders(gamma, d));
    (s.shift_local(d) == *t).then_some(s)
}

/// Does `t`, scoped in a closed context of `m` binders, mention the binder at
/// de Bruijn index `d`?
///
/// The same trick [`strengthen_tm`] uses, narrowed to **one** binder: map
/// index `d` to a marker and every other index to itself, and ask whether the
/// term changed. Precise where `strengthen_ty` is conservative (that one drops
/// a whole *suffix* of binders, so it cannot tell "mentions `f`" from
/// "mentions `a`"), and still no new traversal of the syntax.
///
/// `Term::Zero` is a sound marker: the only position it can land in is one
/// that held `Var(d)`, so the substituted term equals the original exactly
/// when `d` never occurred.
pub(crate) fn mentions_binder(t: &Type, m: u32, d: u32) -> bool {
    let tail = SubstTail::Empty {
        len: m,
        base: CtxBase::Nil,
    };
    let terms = (0..m)
        .map(|k| {
            let idx = m - 1 - k;
            Rc::new(if idx == d {
                Term::Zero
            } else {
                Term::Var(LocalVar(idx))
            })
        })
        .collect();
    t.apply_local(&LocalSubst { tail, terms }) != *t
}

/// [`strengthen_tm`] at the type level.
pub(crate) fn strengthen_ty(gamma: &LocalCtx, t: &Type, d: u32) -> Option<Type> {
    if d == 0 {
        return Some(t.clone());
    }
    let s = t.apply_local(&drop_binders(gamma, d));
    (s.shift_local(d) == *t).then_some(s)
}

/// The identity substitution of `gamma`, weakened so its source is `gamma`
/// extended by `extra` fresh entries: maps a term scoped in `gamma, z` (once
/// `extended`) into `gamma` plus the extra binders.
pub(crate) fn embed(gamma: &LocalCtx, extra: u32) -> LocalSubst {
    let m = gamma.entries.len() as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty {
            len: m + extra,
            base: CtxBase::Nil,
        },
        CtxBase::Var(g) => SubstTail::Wk {
            len: m + extra,
            ctx_var: g,
        },
    };
    let terms = (0..m)
        .map(|j| Rc::new(Term::Var(LocalVar(m + extra - 1 - j))))
        .collect();
    LocalSubst { tail, terms }
}

#[cfg(test)]
mod tests {
    use super::*;
    use heather_kernel::term::GlobalVar;

    fn meta(gamma: &LocalCtx) -> Type {
        Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::GlobalTm {
                var: GlobalVar(0),
                subst: embed(gamma, 0),
            }),
        }
    }

    #[test]
    fn el_meta_learns_the_subjects_code_without_an_elaborator() {
        let gamma = LocalCtx::nil();
        let mut solutions = [Sol::Unsolved];
        unify_ty(&U::syntactic(&gamma), &meta(&gamma), &Type::Nat, 1, 0, &mut solutions);

        assert!(matches!(
            &solutions[0],
            Sol::Solved(term) if **term == Term::TmNat
        ));
    }

    fn app(fun: Term, dom: Type, arg: Term) -> Term {
        Term::App {
            fun: Rc::new(fun),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(dom),
            cod: Rc::new(Type::Nat),
            arg: Rc::new(arg),
        }
    }

    #[test]
    fn flex_spines_specialize_types_but_do_not_guess_value_prefixes() {
        let gamma = LocalCtx::nil();
        let global = Term::GlobalTm {
            // Zero is a committed declaration in the subject, not meta 0.
            var: GlobalVar(0),
            subst: embed(&gamma, 0),
        };
        let Type::El { tm, .. } = meta(&gamma) else {
            unreachable!()
        };
        let pat = app((*tm).clone(), Type::Nat, Term::Zero);
        let specialized = app(global.clone(), Type::Ty(Level::Zero), Term::TmNat);
        let subject = app(specialized.clone(), Type::Nat, Term::Zero);
        let mut solutions = [Sol::Unsolved];
        unify_tm(&U::syntactic(&gamma), &pat, &subject, 1, 0, &mut solutions);
        assert!(matches!(&solutions[0], Sol::Solved(t) if **t == specialized));

        let value_prefix = app(global, Type::Nat, Term::Zero);
        let subject = app(value_prefix, Type::Nat, Term::Zero);
        let mut solutions = [Sol::Unsolved];
        unify_tm(&U::syntactic(&gamma), &pat, &subject, 1, 0, &mut solutions);
        assert!(matches!(solutions[0], Sol::Unsolved));

        let mut withheld = [Sol::Withheld];
        unify_tm(&U::syntactic(&gamma), &pat, &subject, 1, 0, &mut withheld);
        assert!(matches!(withheld[0], Sol::Withheld));
    }

    #[test]
    fn a_guess_waits_while_postponed_and_is_recorded_when_taken() {
        let gamma = LocalCtx::nil();
        let global = Term::GlobalTm { var: GlobalVar(0), subst: embed(&gamma, 0) };
        let Type::El { tm, .. } = meta(&gamma) else {
            unreachable!()
        };
        // `?0(0)` against `g<Nat>(0)`: the type prefix `g<Nat>` is a guess.
        let pat = app((*tm).clone(), Type::Nat, Term::Zero);
        let specialized = app(global.clone(), Type::Ty(Level::Zero), Term::TmNat);
        let subject = app(specialized.clone(), Type::Nat, Term::Zero);
        let postponed = Cell::new(false);
        let u = U { guesses: Guesses::Postpone(&postponed), ..U::syntactic(&gamma) };
        let mut solutions = [Sol::Unsolved];
        unify_tm(&u, &pat, &subject, 1, 0, &mut solutions);
        assert!(matches!(solutions[0], Sol::Unsolved));
        assert!(postponed.get());

        let guessed = RefCell::new(Vec::new());
        let u = U { guesses: Guesses::Record(&guessed), ..U::syntactic(&gamma) };
        unify_tm(&u, &pat, &subject, 1, 0, &mut solutions);
        assert!(matches!(&solutions[0], Sol::Solved(t) if **t == specialized));
        assert_eq!(*guessed.borrow(), vec![0]);

        // `?0(0)` against `g(0)`: the equal-length alignment is decided, and
        // runs while guesses wait.
        let subject = app(global.clone(), Type::Nat, Term::Zero);
        let postponed = Cell::new(false);
        let u = U { guesses: Guesses::Postpone(&postponed), ..U::syntactic(&gamma) };
        let mut solutions = [Sol::Unsolved];
        unify_tm(&u, &pat, &subject, 1, 0, &mut solutions);
        assert!(matches!(&solutions[0], Sol::Solved(t) if **t == global));
        assert!(!postponed.get());
    }

    #[test]
    fn rigid_spines_of_different_lengths_pair_no_arguments() {
        let gamma = LocalCtx::nil();
        // Pattern global 1 is the subject's committed global 0 (`n = 1`).
        let committed = |i| Term::GlobalTm { var: GlobalVar(i), subst: embed(&gamma, 0) };
        let Type::El { tm: hole, .. } = meta(&gamma) else {
            unreachable!()
        };
        // `F(?0, 0)` against `F(1, 0)`: one application, so `?0 := 1`.
        let pat = app(app(committed(1), Type::Nat, (*hole).clone()), Type::Nat, Term::Zero);
        let one = Term::Succ(Rc::new(Term::Zero));
        let same = app(app(committed(0), Type::Nat, one.clone()), Type::Nat, Term::Zero);
        let mut solutions = [Sol::Unsolved];
        unify_tm(&U::syntactic(&gamma), &pat, &same, 1, 0, &mut solutions);
        assert!(matches!(&solutions[0], Sol::Solved(t) if **t == one));
        // `F(?0, 0)` against `F(Nat, 1, 0)`: aligned from the right the hole
        // would meet `1`, which is not its argument
        // (issues/constrained-predicate-expected-type.md).
        let longer = app(
            app(app(committed(0), Type::Ty(Level::Zero), Term::TmNat), Type::Nat, one),
            Type::Nat,
            Term::Zero,
        );
        let mut solutions = [Sol::Unsolved];
        unify_tm(&U::syntactic(&gamma), &pat, &longer, 1, 0, &mut solutions);
        assert!(matches!(solutions[0], Sol::Unsolved));
    }

    #[test]
    fn a_withheld_solution_keeps_a_domain_blocked() {
        let gamma = LocalCtx::nil();
        assert!(zonked(&meta(&gamma), 1, &[Sol::Withheld]).is_none());
    }

    #[test]
    fn partial_subjects_learn_only_committed_solutions() {
        let gamma = LocalCtx::nil();
        for blocked in [Sol::Unsolved, Sol::Withheld] {
            let outer = [blocked];
            let mut u = U::syntactic(&gamma);
            u.subject_metas = Some((1, &outer));
            let mut inner = [Sol::Unsolved];
            unify_ty(&u, &meta(&gamma), &meta(&gamma), 1, 0, &mut inner);
            assert!(matches!(inner[0], Sol::Unsolved), "the two slot-zero occurrences belong to different calls");
        }
        // A solved outer slot contains a committed global at index zero.
        // Partial substitution must keep it distinct from unsolved slot zero.
        let code = Term::GlobalTm { var: GlobalVar(0), subst: embed(&gamma, 0) };
        let outer = [Sol::Solved(Rc::new(code.clone()))];
        let subject = partially_zonked(&meta(&gamma), 1, &outer, &gamma);
        let Type::El { tm, .. } = &subject else { unreachable!() };
        assert!(matches!(&**tm, Term::GlobalTm { var: GlobalVar(1), .. }));
        let mut u = U::syntactic(&gamma);
        u.subject_metas = Some((1, &outer));
        let mut inner = [Sol::Unsolved];
        unify_ty(&u, &meta(&gamma), &subject, 1, 0, &mut inner);
        assert!(matches!(&inner[0], Sol::Solved(t) if **t == code));

        let dependent = Type::Vec {
            level: Level::Zero, elem: Rc::new(Type::Nat), len: Rc::new(Term::Var(LocalVar(0))),
        };
        let pattern = meta(&gamma).apply_local(&embed(&gamma, 1));
        let mut inner = [Sol::Unsolved];
        unify_ty(&u, &pattern, &dependent, 1, 1, &mut inner);
        assert!(matches!(inner[0], Sol::Unsolved), "a solution cannot capture a callback binder");
    }
}
