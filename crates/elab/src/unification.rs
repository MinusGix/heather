//! Implicit-application scratch state and state-free structural unification.

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

    /// No head can be read: every `app@` spine is refused by
    /// [`matching_value_spine`], and nothing else changes.
    #[cfg(test)]
    pub(super) fn syntactic(gamma: &'a LocalCtx) -> Self {
        U { gamma, subject_metas: None, type_args: &|_, _| None, canonical_head: &|_, _| None, respell: &|_| None }
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
        if matches!(sols[var.0 as usize], Sol::Unsolved)
            && *subst == embed(u.gamma, d)
            && let Some(s) = u.subject_ty(subj, d)
            && let Some(c) = code::code_of(&s)
        {
            sols[var.0 as usize] = Sol::Solved(Rc::new(c));
        }
        return;
    }
    // A subject whose code is a β-redex — the type of an `∃`'s proof read
    // off a call, `El(app(λk. P; witness))` — is read as its contractum,
    // which may itself be a former a pattern `Id`/`Π`/… meets
    // (issues/exists-proof-projection-type-not-reduced.md).
    let contracted;
    let subj = match subj {
        Type::El { level, tm } => match beta_head(tm) {
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
                && committed_head(tm, n)
                && zonked_tm(tm, n, sols).is_none() =>
        {
            if let Some(s0) = u.subject_ty(s, d)
                && let Some(r @ Type::El { .. }) = (u.respell)(&s0)
            {
                let r = match u.subject_metas {
                    Some((m, _)) => r.shift_global(m),
                    None => r,
                };
                unify_ty(u, pat, &r.apply_local(&embed(u.gamma, d)), n, d, sols);
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
/// rigid: only the pattern uses indices below `n` as scratch metas.
fn rigid_head(mut t: &Term) -> bool {
    while let Some((fun, _)) = spelling::app_of(t) {
        t = fun;
    }
    matches!(t, Term::Var(_) | Term::GlobalTm { .. })
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
        if matches!(sols[var.0 as usize], Sol::Unsolved)
            && *subst == embed(u.gamma, d)
            && let Some(s) = u.subject_tm(subj, d)
        {
            sols[var.0 as usize] = Sol::Solved(Rc::new(s));
        }
        return;
    }
    // A subject headed by a β-redex has nothing to align until it contracts:
    // the application congruence would pair the pattern's spine against the
    // λ and its argument, and teach the pattern's last argument the redex's
    // (issues/exists-proof-projection-type-not-reduced.md). Contracting the
    // head λs is syntactic and needs no context, so it runs before any other
    // rule, on every pairing; a well-typed subject's head redexes run out.
    if let Some(r) = beta_head(subj) {
        return unify_tm(u, pat, &r, n, d, sols);
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
        _ => {}
    }
}

/// `t` with the β-redexes at the head of its spine contracted, `(λx. b) s ⋯`
/// to `b[s/x] ⋯`, until the head is no λ; `None` when there was none. Only
/// the head: an argument's redexes are reached when the congruence gets to
/// them.
fn beta_head(t: &Term) -> Option<Term> {
    let (fun, arg) = spelling::app_of(t)?;
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

/// Is the spine's head a global, the one head δ can unfold?
fn global_head(mut t: &Term) -> bool {
    while let Some((fun, _)) = spelling::app_of(t) {
        t = fun;
    }
    matches!(t, Term::GlobalTm { .. })
}

/// The two components of a pair in either spelling.
fn pair_of(t: &Term) -> Option<(&Term, &Term)> {
    match t {
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => Some((fst, snd)),
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

/// [`zonked`] for a *term* — same two-marker test, same guarantee: `Some`
/// exactly when every metavariable the term mentions is already solved, in
/// which case the result is scoped in the committed Ψ. Used by the congruence
/// rule, whose witnesses are compared with `==` and so must be real terms.
pub(super) fn zonked_tm(t: &Term, n: u32, sols: &[Sol]) -> Option<Term> {
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
