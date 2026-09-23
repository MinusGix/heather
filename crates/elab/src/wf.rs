//! Tier-1 inductive declarations: the lowering onto the `Wf` former.
//!
//! This module is the mechanization of `docs/inductive-tier1-wf-lowering.md`
//! and is meant to be read against it — the section numbers in the comments
//! are that document's. The doctrine is tier 0's
//! (`inductive.rs`, `issues/inductive-compiler.md`): untrusted like the rest
//! of the elaborator, but a bug here produces a *checked theorem about the
//! wrong type* rather than a rejection, so no clever shortcuts, one function
//! per numbered rule, and every annotation is read off the type being
//! eliminated rather than rebuilt.
//!
//! What is *shared* with tier 0 rather than copied: the shape is
//! `inductive.rs`'s sum-of-Σs with the recursive fields deleted, the arity is
//! its constant-motive case tree at the motive `Nat`, and the step's case
//! tree has the same right-nested shape as `case_tree`. What is shared with
//! the *kernel*: the three types of the step telescope come from
//! `term::wf_step_telescope`, which `typing.rs`, `conv.rs`, `rec.rs` and
//! `reduce.rs` also call. A fifth transcription here would be exactly the
//! drift that arrangement exists to prevent.

#[path = "wf_types.rs"]
mod types;
use types::{EmittedType, StructuralWf};

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalVar, Term, Type, nth, wf_step_telescope};
use heather_syntax::{Arm, Expr, Span};

use crate::inductive::{ConstBody, FieldKind, Inductive, Spine, inject};
use crate::matching::{ChainStep, cov_comps, cov_proj, cov_ty, cov_tuple};
use crate::recursion::{ContainerIh, EqSplit, Guard, GuardKind, WfCov};
use crate::{Alias, Cx, Elaborator, R, embed, err};

/// The pieces every part of the lowering needs, gathered once so that the
/// recursion below carries one reference instead of eight arguments.
///
/// The three telescope types are the kernel's own (§6.1) and are scoped as
/// `wf_step_telescope` returns them:
///
/// ```text
/// cs_ty    over (Γ, a)             = Vec^l(⟦D⟧; n[a/x])
/// ih_ty    over (Γ, a, cs)         = Π(i : Fin n[a/x]). M[nth(…; cs; i)/z]
/// step_ty  over (Γ, a, cs, ih)     = M[sup_f(a; cs)/z]
/// ```
///
/// where `Γ` is `gamma0` — the *ambient* context of the `match`, which every
/// substitution below is expressed relative to.
pub(crate) struct Tel<'a> {
    /// The `match`'s ambient local context.
    pub gamma0: &'a LocalCtx,
    /// `⟦D⟧` **inline** — the `Type::Wf` itself, scoped in `gamma0`. This is
    /// the structural-read copy: `spine` reads the sum-of-Σs out of it and
    /// [`Elaborator::motive_head`] pushes it as a context entry. Never use it
    /// for an emitted annotation; that is [`Tel::emitted`].
    pub structural: StructuralWf<'a>,
    /// `⟦D⟧` as it is **written into emitted terms**, selected by
    /// [`Elaborator::annotation_type`]: a closed code or a parameterized code
    /// application where registered, with component respelling as fallback.
    ///
    /// The two are convertible by construction — the code is `code_of` of
    /// *this* type and the naming registry hands it out only after checking
    /// that — so every use below is a spelling choice and nothing
    /// else. The split is [[wf-field-conversion-cost]]'s whole fix: a tier-1
    /// `match` writes `⟦D⟧` out ~21 times per arm, and each copy carried every
    /// field type verbatim.
    pub emitted: EmittedType,
    /// `l`: the declaration's level, which is also its shape's.
    pub level: Level,
    /// `l'`: the motive's level.
    pub mlvl: Level,
    /// `M`, over `(gamma0, z : ⟦D⟧)`.
    pub motive: Rc<Type>,
    cs_ty: Type,
    ih_ty: Type,
    step_ty: Type,
    /// The declaration's tag spine, scoped in `gamma0`. The **structural-read**
    /// copy: `projection` reads a constructor's Σ components out of it and
    /// `build_fields` checks against them.
    pub spine: Spine,
    /// The same spine as it is **written into emitted terms**: every component
    /// that is a registered declaration's lowering replaced by its reference
    /// (`Elaborator::respell_spine`, the emission copy `build_ctor` has taken
    /// at constructor values since the component-respell round).
    ///
    /// The match lowering was left out of that round by its charter, and this
    /// round's counters are why it is in now: a `match` on a declaration whose
    /// constructors carry a `Wf`-lowered field wrote that field type verbatim
    /// into every `Case`, every `Inr` and every injection — Θ(arms²) copies of
    /// `⟦T⟧`, and most of a lowered body's node mass, measured
    /// (`docs/wf-shape-code-design.md` §3.4).
    pub spine_emit: Spine,
    /// The `Wf` slot pair as it is written into emitted terms, kept because
    /// the course-of-values lowering has to rebuild the `sup_f` the telescope
    /// states its step at ([`Tel::value_at`]) with those very slots.
    slots: (Rc<Type>, Rc<Term>),
    /// What this `match` carries beyond the ordinary lowering
    /// (`docs/list-course-of-values-design.md`). [`TelRec::None`] for every
    /// `match` written before the window existed.
    rec: TelRec<'a>,
}

/// [`WfRec`] once `build_elim_wf` has respelled the motive: the window's
/// components are built from the *respelled* motive, or the types the arms
/// annotate with would not be the ones the eliminator's own type states.
enum TelRec<'a> {
    None,
    Cov {
        d: usize,
        step: &'a ChainStep,
        /// `M` as the source wrote it, over `(gamma0, z)`, respelled.
        /// [`Tel::motive`] is the Σ-tower built from it.
        plain: Rc<Type>,
    },
    Convoy {
        convoy: &'a WfConvoy,
        /// The level the *arm bodies* live at. [`Tel::mlvl`] is the motive's,
        /// which for a convoyed `match` is the max of this and the window's.
        body_lvl: Level,
    },
}

/// What a `match` on a tier-1 inductive carries beyond the ordinary lowering.
/// The two are exclusive: a `match` that descends on a parameter sets a window
/// up, a nested `match` on the chain's end passes one down.
pub(crate) enum WfRec<'a> {
    /// The ordinary lowering, byte for byte.
    None,
    /// A course-of-values recursion carrying `d` values
    /// (`docs/list-course-of-values-design.md` §3).
    Cov { d: usize, step: ChainStep },
    /// A nested `match` on the chain's end, convoying the enclosing
    /// recursion's window in as an argument (§4).
    Convoy(&'a WfConvoy),
}

/// The enclosing recursion's window of past values, as a nested `match` on the
/// chain's end needs it (`docs/list-course-of-values-design.md` §4). The `Nat`
/// twin is `matching::routes`'s `Convoy`, and every field here means what its
/// field there means.
pub(crate) struct WfConvoy {
    dec: usize,
    /// The chain so far, as terms, scoped in this `match`'s own context.
    chain: Vec<Rc<Term>>,
    /// How many values are carried.
    d: usize,
    lvl: Level,
    /// The recursion's motive reindexed into the context this `match` sits in,
    /// scoped in (that context, z)…
    motive: Rc<Type>,
    /// …and as it was written, for the guards this `match` hands to its arms:
    /// they must be able to reindex it again, deeper in.
    outer_motive: Rc<Type>,
    gamma: LocalCtx,
    /// `tail_D` reindexed here, and as it was written, for the same reason.
    step: ChainStep,
    outer_tail: Rc<Term>,
    /// The window itself, at this `match`'s context.
    tuple: Term,
    /// `λ y. …` — where the window's anchor and the goal's sit, seen from a
    /// term at this `match`'s scrutinee. Copies of [`WfCov::window`] and
    /// [`WfCov::goal`], shifted.
    window: Rc<Term>,
    goal: Rc<Term>,
    generalized: Option<Rc<Vec<usize>>>,
}

impl WfConvoy {
    /// An anchor applied by substitution: `t` is scoped `extra` binders past
    /// `gamma`, which is this `match`'s own ambient context. No β-redex is
    /// emitted — the anchors are λs only so that they shift like closed
    /// terms.
    fn at(anchor: &Rc<Term>, gamma: &LocalCtx, extra: u32, t: Term) -> Term {
        let Term::Lam { body, .. } = &**anchor else {
            unreachable!("an anchor is built as a λ and only ever shifted")
        };
        body.apply_local(&embed(gamma, extra).extended(Rc::new(t)))
    }

    fn window(&self, gamma: &LocalCtx, extra: u32, t: Term) -> Term {
        Self::at(&self.window, gamma, extra, t)
    }

    fn goal(&self, gamma: &LocalCtx, extra: u32, t: Term) -> Term {
        Self::at(&self.goal, gamma, extra, t)
    }
}

impl Tel<'_> {
    /// The scrutinee this branch stands for: `sup_f(ℓᵢ; cs')`, spelled exactly
    /// as `wf_step_telescope_at` states `step_ty` at it — the same slots
    /// through the same shift — so that the window's components built here and
    /// the obligation the telescope hands down agree *syntactically* rather
    /// than only by conversion.
    fn value_at(&self, inj: &Rc<Term>, d_body: u32) -> Term {
        let whole = Type::Wf {
            level: self.level.clone(),
            shape: Rc::clone(&self.slots.0),
            arity: Rc::clone(&self.slots.1),
        };
        // Through the `Wf`, so that the arity — scoped under the shape's
        // binder — crosses the right number of them.
        let Type::Wf { shape, arity, .. } = whole.shift_local(d_body) else {
            unreachable!("shifting a Wf yields a Wf")
        };
        Term::Supf {
            level: self.level.clone(),
            shape,
            arity,
            label: Rc::new(inj.shift_local(2)),
            children: Rc::new(Term::Var(LocalVar(1))),
        }
    }

    /// This arm's own constructor with its own child back in the recursive
    /// field: `sup_f(ℓᵢ; (nth cs' ι₀, ⟨⟩))`, scoped in the branch itself.
    fn rebuilt_here(&self, inj: &Rc<Term>, d_body: u32, child: &Rc<Term>) -> Term {
        self.supf_over(inj, d_body, d_body, Rc::clone(child))
    }

    /// This arm's own constructor with `y` in its recursive field:
    /// `sup_f(ℓᵢ; (y, ⟨⟩))`. The `Wf` counterpart of `Nat`'s `Succ(y)`, and
    /// what §4's re-anchoring rebuilds — the payload travels as the label it
    /// already is, so nothing is re-elaborated and only the children tuple is
    /// new. Scoped in the branch plus the convoy binder plus `y`.
    fn rebuilt_at(&self, inj: &Rc<Term>, d_body: u32) -> Term {
        self.supf_over(inj, d_body, d_body + 2, Rc::new(Term::Var(LocalVar(0))))
    }

    /// `sup_f(ℓᵢ; (child, ⟨⟩))` at depth `up`, for a constructor with exactly
    /// one recursive field — every constructor a [`chain_shaped`] declaration
    /// has one of. Only the children tuple is new: the payload travels as the
    /// label `inj` it already is, so nothing is re-elaborated.
    fn supf_over(&self, inj: &Rc<Term>, d_body: u32, up: u32, child: Rc<Term>) -> Term {
        let whole = Type::Wf {
            level: self.level.clone(),
            shape: Rc::clone(&self.slots.0),
            arity: Rc::clone(&self.slots.1),
        };
        let Type::Wf { shape, arity, .. } = whole.shift_local(up) else {
            unreachable!("shifting a Wf yields a Wf")
        };
        let elem = self.emitted.shift_local(up).into_type();
        // `Vec(T; S 0) ⇝ Σ(_ : T). Vec(T; 0)`, and a Σ's second component
        // binds, so the tail sits one level deeper (§5).
        let children = Term::Pair {
            fst_level: self.level.clone(),
            snd_level: self.level.clone(),
            fst_ty: Rc::new(elem.clone()),
            snd_ty: Rc::new(Type::Vec {
                level: self.level.clone(),
                elem: Rc::new(elem.shift_local(1)),
                len: Rc::new(Term::Zero),
            }),
            fst: child,
            snd: Rc::new(Term::Triv {
                level: self.level.clone(),
            }),
        };
        Term::Supf {
            level: self.level.clone(),
            shape,
            arity,
            // `inj` is scoped where the branch's own binders start, which is
            // `d_body - 2`; `up` is here.
            label: Rc::new(inj.shift_local(up - (d_body - 2))),
            children: Rc::new(children),
        }
    }

    /// The Π-type of a branch body before its two λs: `P(v)` of §6.2, for a
    /// *fully injected* `v : S` scoped `d` binders past `gamma0`.
    ///
    /// The three instantiations differ only in how deep they sit, and each
    /// maps the telescope's own binders (`a`, `cs`, `ih`) to what stands for
    /// them here. Writing them out rather than folding them is deliberate:
    /// this is the de Bruijn arithmetic the issue's hazard list warns about.
    fn at(&self, inj: &Rc<Term>, d: u32) -> (Type, Type, Type) {
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        // cs' : cs_ty[v/a], in the branch context itself.
        let cs = self
            .cs_ty
            .apply_local(&embed(self.gamma0, d).extended(Rc::clone(inj)));
        // ih' : ih_ty[v/a, cs'/cs], one binder deeper (cs' is Var 0).
        let ih = self.ih_ty.apply_local(
            &embed(self.gamma0, d + 1)
                .extended(Rc::new(inj.shift_local(1)))
                .extended(var(0)),
        );
        // the body : step_ty[v/a, cs'/cs, ih'/ih], two binders deeper.
        let step = self.step_ty.apply_local(
            &embed(self.gamma0, d + 2)
                .extended(Rc::new(inj.shift_local(2)))
                .extended(var(1))
                .extended(var(0)),
        );
        (cs, ih, step)
    }
}

/// What a branch of the step's case tree computes. The two share the whole
/// eliminator — the telescope, the case tree, the `cs`/`ih` generalization
/// and the two trailing applications — and differ only in the body at each
/// constructor.
pub(crate) enum Branches<'a> {
    /// `match`: the surface arms, already in declaration order (§6.3).
    Arms(&'a [&'a Arm]),
    /// A body the caller builds, for an eliminator on this declaration that is
    /// not a `match` on it: the family over a declared index and its derived
    /// eliminator both case on the *index* type here
    /// (docs/inductive-indexed-lowering.md §8.2), so the branch body is an
    /// indexed-family thing and only the `cs`/`ih` threading is tier 1's.
    ///
    /// Called as `(bcx, tel, i, value, d_body, body_ty)` with `bcx` the branch
    /// context, `i` the constructor, `value : ⟦cᵢ⟧` and `d_body` its depth past
    /// `gamma0`, and `body_ty` the obligation. By the branch convention the
    /// refined `cs'` is `Var 1` and `ih'` is `Var 0` in `bcx`.
    #[allow(clippy::type_complexity)]
    Custom(&'a dyn Fn(&Cx, &Tel, usize, &Rc<Term>, u32, &Type) -> R<Term>),
    /// Injectivity at a recursive field (§7.2): the `t`-th child at
    /// constructor `i`, and the totality default elsewhere. It has to go
    /// through the generalization too — reading a child out of `cs` needs the
    /// *literal* arity, and outside a tag branch that arity is stuck on a
    /// variable.
    Child {
        i: usize,
        t: usize,
        default: Rc<Term>,
    },
    /// `tail_D` (`docs/list-course-of-values-design.md` §2): the one child at
    /// *every* recursive constructor, and `default` — the scrutinee itself —
    /// at every base one, so that `tail_D(Nil) ⇝ Nil` the way `pred 0 ⇝ 0`.
    ///
    /// [`Branches::Child`] cannot stand in: it names one constructor, and a
    /// chain-shaped declaration may have several recursive ones
    /// (`Run { Stop, Step(p, next), Skip(next) }`). Only reached for a
    /// declaration [`chain_shaped`] accepted, so every arity here is 0 or 1.
    Tail { default: Rc<Term> },
}

/// Is `ind` **chain-shaped** — does every constructor carry at most one
/// recursive field and no container (`docs/list-course-of-values-design.md`
/// §1)?
///
/// Only such a declaration has a *chain* for the course-of-values window to
/// walk. A branching constructor's window would be a tree of values, which is
/// a different tupling and has no customer; a container field is a group of
/// children rather than one, and a self-call over it maps rather than
/// descends (`docs/container-fields.md` §4.2).
pub(crate) fn chain_shaped(ind: &Inductive) -> bool {
    ind.ctors
        .iter()
        .all(|c| c.arity() <= 1 && c.container().is_none())
}

impl Elaborator {
    // -- constructors (§5) --------------------------------------------------

    /// The children tuple `(r₁, (r₂, … (r_m, ⟨⟩)))` at `Vec^l(⟦D⟧; m)`, built
    /// at the *literal* arity `m` rather than at `n[ℓᵢ/x]`. The two are
    /// convertible — the arity is a `Case` on an injection, so it β-reduces to
    /// the literal, and `Vec` reduces on the whnf of its length — and the
    /// literal is the one the kernel can unfold to a Σ-chain.
    ///
    /// `d_ty` is `⟦D⟧` (the whole `Wf`), scoped in `cx`.
    ///
    /// The two spellings are split here for the reason §3.1 gives: the
    /// children are **checked** against `⟦D⟧`, and a checking position is a
    /// structural read (`Cons(x, Cons(y, Nil))` resolves its inner
    /// constructor against the expected type), so `elab_check` keeps the
    /// inline `Wf`; the `Vec`/`Pair` annotations the tuple carries are pure
    /// emission and take the reference.
    pub(crate) fn build_children(
        &self,
        cx: &Cx,
        d_ty: &Type,
        level: &Level,
        args: &[Expr],
        container: Option<(&Expr, Rc<Term>)>,
        span: Span,
    ) -> R<Term> {
        let _ = span;
        // Emitted tuple annotations use the same naming policy as matches;
        // structural checking below still reads d_ty.
        let emit = self.annotation_type(cx, d_ty, 0);
        // The tuple's terminator. Tier 1 ends with `⟨⟩ : Unit^l` — which
        // `Vec^l(T; 0) ⇝ Unit^l` makes the *zero* case of a container tail,
        // so the two are one code path (docs/container-fields.md §3.4).
        // (`Triv` carries the level since route (a) of
        // issues/unit-level-and-vec-preservation.md; a `Triv` at 0 here would
        // be exactly the defect that round closed.)
        let (mut acc, mut tail_len) = match &container {
            Some((arg, len)) => {
                // A **checking** position (the container argument is written
                // at the surface), so the element type stays inline: checking
                // a vector literal checks each element against it, and that is
                // a structural read.
                let vec_ty = Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(d_ty.clone()),
                    len: Rc::clone(len),
                };
                (self.elab_check(cx, arg, &vec_ty, level)?, (**len).clone())
            }
            None => (
                Term::Triv {
                    level: level.clone(),
                },
                Term::Zero,
            ),
        };
        for arg in args.iter().rev() {
            let child = self.elab_check(cx, arg, d_ty, level)?;
            let tail = tail_len.clone();
            acc = Term::Pair {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::new(emit.clone()),
                // `Vec(T; S k) ⇝ Σ(_ : T). Vec(T; k)` and a Σ's second
                // component *binds*, so the tail type sits one level deeper
                // than the ambient (§5).
                snd_ty: Rc::new(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(emit.shift_local(1)),
                    len: Rc::new(tail.shift_local(1)),
                }),
                fst: Rc::new(child),
                snd: Rc::new(acc),
            };
            tail_len = Term::Succ(Rc::new(tail_len));
        }
        Ok(acc)
    }

    // -- match (§6) ---------------------------------------------------------

    /// `match` on a tier-1 inductive: one `elim_Wf` whose step cases on the
    /// tag with `cs` and `ih` generalized (§6.2).
    ///
    /// `arms` is already permuted into declaration order and checked for
    /// completeness, duplication and binder arity by the tier-0 entry point;
    /// `scrut_ty` is the whnf'd `⟦D⟧`, and `motive` is scoped over
    /// `(cx.gamma, z : ⟦D⟧)`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_wf(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[&Arm],
        scrut: Term,
        scrut_ty: &Type,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        // Does this `match` descend on one of the enclosing declaration's own
        // parameters? If so, a self-call in an arm is the ih (§6.4).
        let dec = crate::recursion::descends_on_param(cx, &scrut);
        let Type::Wf { level, .. } = scrut_ty else {
            return err(
                "internal: a recursive declaration did not lower to a `Wf`",
                span,
            );
        };
        let level = level.clone();
        // The motive, respelled once here rather than twice: `build_elim_wf`
        // respells again and `annotation_type` is idempotent, but the window's
        // components have to be built from the *respelled* spelling, and this
        // is where both halves can see it.
        let plain = Rc::new(self.annotation_type(cx, &motive, 1));
        // How many past values the arms read (`docs/list-course-of-values-design.md`
        // §3). `1` is the ordinary recursion and emits exactly the term it
        // always did; more makes the recursor carry a tuple.
        let d = match dec {
            Some(dec) if chain_shaped(ind) => self.cov_depth_wf(cx, ind, arms, dec),
            _ => 1,
        };
        // A nested `match` on the chain's end, with values below it still
        // uncollected: it must **convoy** them, or its arms cannot see that the
        // value one below the arm's child is the value at the child's own
        // child (§4).
        let convoy = if dec.is_none() {
            self.wf_chain_convoy(cx, &scrut)
        } else {
            None
        };
        let rec = match (&convoy, d) {
            (Some(convoy), _) => WfRec::Convoy(convoy),
            (None, 1) => WfRec::None,
            (None, d) => WfRec::Cov {
                d,
                step: ChainStep::Tail(Rc::new(
                    self.tail_term(cx, ind, scrut_ty, &level, span)?,
                )),
            },
        };
        let elim = self.build_elim_wf(
            cx,
            ind,
            scrut_ty,
            (*plain).clone(),
            mlvl.clone(),
            scrut.clone(),
            &Branches::Arms(arms),
            dec,
            &rec,
            span,
        )?;
        match &rec {
            WfRec::None => Ok(elim),
            // The source's `match` is the *first* component of what the
            // recursor now computes, so the transformation stays local to this
            // expression: its type is still `M[scrut/z]`.
            WfRec::Cov { d, step } => {
                let comps = cov_comps(&cx.gamma, step, &plain, *d, 0, &scrut);
                Ok(cov_proj(&comps, &mlvl, elim, 0))
            }
            // …and the window goes in, which is what refines it.
            WfRec::Convoy(convoy) => {
                let at = convoy.window(&cx.gamma, 0, scrut.clone());
                let comps = cov_comps(&cx.gamma, &convoy.step, &convoy.motive, convoy.d, 0, &at);
                Ok(crate::spelling::checked_app(
                    Rc::new(elim),
                    convoy.lvl.clone(),
                    mlvl.clone(),
                    Rc::new(cov_ty(&comps, &convoy.lvl)),
                    // The whole `match` computes the enclosing recursion's
                    // motive at the anchor, which is `chain[0]` — the very
                    // obligation the enclosing arm is being checked against.
                    Rc::new(convoy.motive.apply_local(
                        &embed(&cx.gamma, 1).extended(Rc::new(convoy.goal(
                            &cx.gamma,
                            1,
                            scrut.shift_local(1),
                        ))),
                    )),
                    Rc::new(convoy.tuple.clone()),
                ))
            }
        }
    }

    /// A nested `match` on the enclosing arm's recursive child continues the
    /// chain — but only if the values the enclosing recursion carries are
    /// *passed through* this `match`, since only then does the component one
    /// below the child reduce, at the arm that knows the child is
    /// `Cons(h, t)`, to the value at `t` (§4).
    ///
    /// `None` when the enclosing recursion has nothing left to hand down,
    /// which is every ordinary one-step recursion.
    fn wf_chain_convoy(&self, cx: &Cx, scrut: &Term) -> Option<WfConvoy> {
        let g = cx.guard.clone()?;
        let GuardKind::Wf {
            depth,
            cov: Some(window),
            ..
        } = &g.kind
        else {
            return None;
        };
        // Nothing below the chain's end is carried: the ordinary recursion,
        // which a nested `match` changes nothing about.
        if window.comps.len() <= window.chain.len() {
            return None;
        }
        let by = (cx.names.len() - depth) as u32;
        // By *term*, never by name: an inner binder that shadows the arm's own
        // is a different alias and does not continue the chain.
        if window.chain.last()?.shift_local(by) != *scrut {
            return None;
        }
        let reindex = |t: &Rc<Term>| {
            t.apply_local(
                &embed(&window.gamma, by + 1).extended(Rc::new(Term::Var(LocalVar(0)))),
            )
        };
        Some(WfConvoy {
            dec: g.dec,
            chain: window
                .chain
                .iter()
                .map(|t| Rc::new(t.shift_local(by)))
                .collect(),
            d: window.comps.len(),
            lvl: window.mlvl.clone(),
            motive: Rc::new(window.motive.apply_local(
                &embed(&window.gamma, by + 1).extended(Rc::new(Term::Var(LocalVar(0)))),
            )),
            outer_motive: Rc::clone(&window.motive),
            gamma: window.gamma.clone(),
            step: ChainStep::Tail(Rc::new(reindex(&window.tail))),
            outer_tail: Rc::clone(&window.tail),
            tuple: window.tuple.shift_local(by),
            window: Rc::new(window.window.shift_local(by)),
            goal: Rc::new(window.goal.shift_local(by)),
            generalized: g.generalized.clone(),
        })
    }

    /// How deep into the chain this `match`'s self-calls reach, over all its
    /// arms: the `Wf` case of `cov_depth` (`Nat` design §6, list design §5).
    ///
    /// Each recursive arm contributes the depth its own body reaches from its
    /// own child binder, and the window is sized for the deepest — one motive
    /// serves every arm, so one depth does. Syntactic and a sizing decision
    /// only, for exactly the reasons the `Nat` scan states: wrong in either
    /// direction is safe, because what a call *lowers to* is decided by
    /// `elab_self_call` comparing terms.
    fn cov_depth_wf(&self, cx: &Cx, ind: &Inductive, arms: &[&Arm], dec: usize) -> usize {
        let mut d = 1usize;
        for (i, arm) in arms.iter().enumerate() {
            let ctor = &ind.ctors[i];
            let Some(field) = ctor.kind.iter().position(|k| *k == FieldKind::Plain) else {
                continue;
            };
            let Some(binder) = arm.binders.get(field) else {
                continue;
            };
            d = d.max(self.cov_depth(cx, &arm.body, binder.name(), dec, Some(ind)));
        }
        d
    }

    /// The `t`-th child of constructor `i` as a *total* function of `⟦D⟧`
    /// (§7.2), for injectivity. `d_ty`, `default` and `scrut` are all scoped
    /// in `cx`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn child_projection(
        &self,
        cx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        level: &Level,
        i: usize,
        t: usize,
        default: Rc<Term>,
        scrut: Term,
        span: Span,
    ) -> R<Term> {
        // A constant motive at `⟦D⟧` — the projection is not an inductive
        // argument, so nothing here reads `ih`. The motive is an emitted
        // annotation (it lands in the `ElimWf`'s motive slot), so it takes the
        // reference where one exists; `d_ty` itself stays inline because
        // `build_elim_wf` destructures it.
        let motive = self.annotation_type(cx, d_ty, 0).shift_local(1);
        self.build_elim_wf(
            cx,
            ind,
            d_ty,
            motive,
            level.clone(),
            scrut,
            &Branches::Child { i, t, default },
            None,
            &WfRec::None,
            span,
        )
    }

    /// `tail_D`, the projection that plays `pred` for a chain-shaped `Wf`
    /// (`docs/list-course-of-values-design.md` §2), as a term over
    /// `(cx.gamma, z : ⟦D⟧)`:
    ///
    /// ```text
    /// tail_D(z) = elim_Wf(λ _. ⟦D⟧; case tag of
    ///                 recursive ctor ⇒ the one child | base ctor ⇒ z; z)
    /// ```
    ///
    /// Two computation facts come out of it, and they are the ones the window
    /// needs: `tail_D(Cons(h, t)) ⇝ t` is `elim_Wf` β on a `sup`, and at a
    /// base constructor `tail_D` is the scrutinee itself — the `z` the outer
    /// binder supplies, which is what makes every component of a base arm's
    /// tuple sit at one and the same type.
    ///
    /// It goes through [`Self::build_elim_wf`] and not `const_elim_wf`, per
    /// §7's correction: a *constant motive* frees the step from `ih` but not
    /// from `cs`, and reading a child out of `cs` needs the literal arity that
    /// only a tag branch has.
    pub(crate) fn tail_term(
        &self,
        cx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        level: &Level,
        span: Span,
    ) -> R<Term> {
        let mut zcx = cx.clone();
        zcx.push("#z".into(), d_ty.clone(), level.clone());
        let under_z = d_ty.shift_local(1);
        let z = Rc::new(Term::Var(LocalVar(0)));
        // The motive is `⟦D⟧` itself, constant in the eliminator's own binder
        // — an emitted annotation, so it takes the reference where there is
        // one, exactly as `child_projection`'s does.
        let motive = self.annotation_type(&zcx, &under_z, 0).shift_local(1);
        self.build_elim_wf(
            &zcx,
            ind,
            &under_z,
            motive,
            level.clone(),
            (*z).clone(),
            &Branches::Tail {
                default: Rc::clone(&z),
            },
            None,
            &WfRec::None,
            span,
        )
    }

    /// The match motive's **head**, for phase 3's "is this an equation?" test
    /// (docs/container-proofs.md §5).
    ///
    /// Structural first, exactly as `record_of_at`: a written `a = b` is
    /// already an `Id` and nothing is paid. Only a motive that arrived as a
    /// *code* — `El (Agree z)` for a named statement
    /// (`docs/types-as-expressions.md`), or `El` of a β-redex for one reached
    /// through a `Val -> Type` value (`docs/record-type-values.md` §6) —
    /// reduces, and then `whnf` is the right amount: `Id` is a weak-head
    /// normal form, so this cannot overshoot the shape it is looking for.
    ///
    /// The motive is scoped `(Γ₀, z : ⟦D⟧)`, which is not any context this
    /// walk carries, so it is rebuilt here from the two pieces `Tel` already
    /// holds. Failure is not an error: an unreducible motive is simply not an
    /// equation, which is the answer the caller wanted anyway.
    fn motive_head<'t>(&self, tel: &'t Tel<'_>) -> std::borrow::Cow<'t, Type> {
        if !matches!(&*tel.motive, Type::El { .. }) {
            return std::borrow::Cow::Borrowed(&tel.motive);
        }
        let mut gamma = tel.gamma0.clone();
        gamma.entries.push(heather_kernel::term::CtxEntry {
            ty: Rc::new(tel.structural.as_type().clone()),
            level: tel.level.clone(),
        });
        match self.semantic_oracle().whnf_type(&gamma, &tel.motive) {
            Ok(t) => std::borrow::Cow::Owned(t),
            Err(_) => std::borrow::Cow::Borrowed(&tel.motive),
        }
    }

    /// The eliminator both of the above are (§6.2): one `elim_Wf` whose step
    /// cases on the tag with `cs` and `ih` generalized in the case motive.
    /// Outside a tag branch the arity `n[a/x]` is stuck on a variable, so
    /// neither `Vec` nor `Fin` reduces and neither the children tuple nor the
    /// ih can be projected; inside branch `i` the arity is the literal `mᵢ`
    /// and everything unfolds. That is why the generalization is not
    /// stylistic.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_elim_wf(
        &self,
        cx: &Cx,
        ind: &Inductive,
        scrut_ty: &Type,
        motive: Type,
        mlvl: Level,
        scrut: Term,
        branches: &Branches,
        dec: Option<usize>,
        rec: &WfRec,
        span: Span,
    ) -> R<Term> {
        let Type::Wf {
            level,
            shape,
            arity,
        } = scrut_ty
        else {
            return err(
                "internal: a recursive declaration did not lower to a `Wf`",
                span,
            );
        };
        // The *motive* is `⟦D'⟧` for whatever the arms return, and it is the
        // single largest occurrence site of all: it is instantiated once per
        // `Case` node of the tag tree, twice more per branch (the two λ
        // domains), and twice again in `apply_cs_ih`. Respelling it needs no
        // tag from the caller — `tag_of` reads it out of the type, and
        // `closed_type_ref` declines unless the type *is* that declaration's
        // registered lowering.
        //
        // The `shift_local(1)` is not cosmetic: the motive is scoped over
        // `(Γ₀, z : ⟦D⟧)`, one binder past `cx`, and `gen_ref` stamps the
        // reference's substitution tail with `cx`'s own length. Without it the
        // kernel answers `SubstMismatch` at every `match` — which is the good
        // failure mode, but a failure mode.
        //
        // **Component-wise**, not whole-type only: a `fn` returning a function
        // (`pick_arm(arms: Ir) -> Nat -> Ir`) has the motive `Π(Nat). ⟦Ir⟧`,
        // which is not itself any declaration's lowering, and the whole-type
        // respell declined on it — leaving the single largest type in the file
        // written out at every instantiation of the motive. `depth` is 1, the
        // motive's own `z` binder: `respell_ty_deep` shifts the *references* by
        // it rather than the result, which is why this is not the
        // `shift_local(1)` the whole-type version needed.
        let plain = Rc::new(self.annotation_type(cx, &motive, 1));
        // The motive of the recursor actually emitted. Three shapes, and the
        // first is what every `match` on a tier-1 inductive has always
        // emitted (`docs/list-course-of-values-design.md` §3–§4):
        //   ordinary : M
        //   window   : Σ(M[z], M[tail z], …)   — the carried values
        //   convoy   : T_outer(anchor z) -> M[z]  — the window passed in
        let (motive, mlvl, rec) = match rec {
            WfRec::None => (Rc::clone(&plain), mlvl, TelRec::None),
            WfRec::Cov { d, step } => {
                let comps = cov_comps(
                    &cx.gamma,
                    step,
                    &plain,
                    *d,
                    1,
                    &Term::Var(LocalVar(0)),
                );
                (
                    Rc::new(cov_ty(&comps, &mlvl)),
                    mlvl,
                    TelRec::Cov {
                        d: *d,
                        step,
                        plain: Rc::clone(&plain),
                    },
                )
            }
            WfRec::Convoy(convoy) => {
                let at = convoy.window(&cx.gamma, 1, Term::Var(LocalVar(0)));
                let carried = cov_ty(
                    &cov_comps(&cx.gamma, &convoy.step, &convoy.motive, convoy.d, 1, &at),
                    &convoy.lvl,
                );
                // The codomain is the **enclosing recursion's** motive at this
                // `match`'s anchor, not the motive synthesized from the goal.
                // Those are convertible — the goal was `M[chain[0]]` and
                // `anchor(chain-end)` is `chain[0]` — and the anchored
                // spelling is the one that *refines*: a `Wf` arm's goal sits
                // at `sup_f(ℓ; cs')`, where the child is `nth(cs'; ι₀)` and
                // not a subterm, so synthesis has to recover the scrutinee
                // out of a reduced goal and at depth it does not. Rebuilding
                // it here is the §4 anchoring again, one level up.
                let anchored = convoy
                    .motive
                    .apply_local(&embed(&cx.gamma, 2).extended(Rc::new(convoy.goal(
                        &cx.gamma,
                        2,
                        Term::Var(LocalVar(1)),
                    ))));
                let pi = Type::Pi {
                    dom_level: convoy.lvl.clone(),
                    cod_level: convoy.lvl.clone(),
                    dom: Rc::new(carried),
                    cod: Rc::new(anchored),
                };
                let rec = TelRec::Convoy {
                    convoy,
                    body_lvl: convoy.lvl.clone(),
                };
                (Rc::new(pi), convoy.lvl.clone(), rec)
            }
        };
        // Name both closed and parameterized recursive types in the children
        // telescope. An inline List<CallInstruction> here repeats the entire
        // instruction payload in Vec/nth annotations (call_run_checked).
        // Structural readers below keep scrut_ty.
        let structural = StructuralWf::new(scrut_ty).expect("the Wf was checked above");
        let emitted = structural.annotation(self, cx);
        // The `Wf` slot pair as it is **written into emitted terms**
        // (`docs/wf-shape-code-design.md` §3.2): `El (D#shape^δ)` and
        // `app(D#arity^δ; x₀)` where this declaration has the pair registered,
        // the inline slots otherwise. The structural reads a few lines down —
        // `cx3`'s `#a` entry, `spine` — take `shape`/`arity` themselves, per
        // §4's line.
        //
        // A **monomorphized** `Wf` (`List<Node>`) has no pair to name; its
        // slots then take the same component respell the spine's emission
        // copy takes below (`respell_spine`), or neither does. The kernel
        // rebuilds `Fin(n[ℓ/x])` for the ih from *this* arity at every
        // reduction of the eliminator, and a projection chain written off
        // that reduct met the label's respelled injections with the inline
        // `Case` annotations of an inline arity (`Sum` vs `Sum`, 300 queries
        // of the five-node FunctionIR/x86 module after the value sites
        // agreed, 2026-09-06; issues/emission-site-respell-audit.md).
        let (shape_e, arity_e) = match self.wf_slot_refs(cx, shape, arity) {
            Some((s, a)) => (Rc::new(s), Rc::new(a)),
            None => self
                .emit_wf_slots(cx, shape, arity, 0)
                .unwrap_or_else(|| (Rc::clone(shape), Rc::clone(arity))),
        };
        let (cs_ty, ih_ty, step_ty) = structural.telescope(
            &cx.gamma, &mlvl, &motive, &emitted, (&shape_e, &arity_e),
        );
        let spine = self.spine(scrut_ty, level, ind.ctors.len(), span)?;
        let spine_emit = self.respell_spine(cx, &spine);
        let tel = Tel {
            gamma0: &cx.gamma,
            structural,
            emitted,
            level: level.clone(),
            mlvl: mlvl.clone(),
            motive: Rc::clone(&motive),
            spine,
            spine_emit,
            cs_ty,
            ih_ty,
            step_ty,
            slots: (Rc::clone(&shape_e), Rc::clone(&arity_e)),
            rec,
        };
        // Γ₃ = (Γ, a : S, cs : cs_ty, ih : ih_ty) — the step's context, and
        // the kernel's, verbatim (typing.rs's `elim_Wf` rule).
        let mut cx3 = cx.clone();
        cx3.push("#a".into(), (**shape).clone(), tel.level.clone());
        cx3.push("#cs".into(), tel.cs_ty.clone(), tel.level.clone());
        cx3.push("#ih".into(), tel.ih_ty.clone(), tel.mlvl.clone());

        // The case motive `P`, over (Γ₃, z : S): the telescope re-abstracted
        // at `z` in place of `a`. It lives at `l ⊔ l'` — a Π at the max of
        // its ends, twice.
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        let (p_cs, p_ih, p_step) = {
            let cs = tel
                .cs_ty
                .apply_local(&embed(tel.gamma0, 4).extended(var(0)));
            let ih = tel
                .ih_ty
                .apply_local(&embed(tel.gamma0, 5).extended(var(1)).extended(var(0)));
            let step = tel.step_ty.apply_local(
                &embed(tel.gamma0, 6)
                    .extended(var(2))
                    .extended(var(1))
                    .extended(var(0)),
            );
            (cs, ih, step)
        };
        let p_motive = Type::Pi {
            dom_level: tel.level.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(p_cs),
            cod: Rc::new(Type::Pi {
                dom_level: tel.mlvl.clone(),
                cod_level: tel.mlvl.clone(),
                dom: Rc::new(p_ih),
                cod: Rc::new(p_step),
            }),
        };
        let plvl = Level::max(tel.level.clone(), tel.mlvl.clone());

        let cased = self.wf_case_tree(
            &cx3,
            ind,
            branches,
            &tel,
            dec,
            0,
            p_motive,
            &plvl,
            var(2),
            3,
            span,
        )?;
        let step = self.apply_cs_ih(&tel, cased);

        Ok(Term::ElimWf {
            level: tel.level.clone(),
            motive_level: tel.mlvl.clone(),
            shape: shape_e,
            arity: arity_e,
            motive,
            step: Rc::new(step),
            scrut: Rc::new(scrut),
        })
    }

    /// `(P-case on a) cs ih` (§6.2): the two applications that re-connect the
    /// generalized `cs'`/`ih'` to the step's real ones. Both `cod`
    /// annotations **bind their own argument**, so they sit one level deeper
    /// than `Γ₃` — the de Bruijn slip both kernel acceptance tests made first.
    fn apply_cs_ih(&self, tel: &Tel, cased: Term) -> Term {
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        let g = tel.gamma0;
        // Domains, over Γ₃ itself: a = 2, cs = 1.
        let dom_cs = tel.cs_ty.apply_local(&embed(g, 3).extended(var(2)));
        let dom_ih = tel
            .ih_ty
            .apply_local(&embed(g, 3).extended(var(2)).extended(var(1)));
        // First `cod`, over (Γ₃, cs''): a = 3, cs = cs'' = 0.
        let cod1 = Type::Pi {
            dom_level: tel.mlvl.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(
                tel.ih_ty
                    .apply_local(&embed(g, 4).extended(var(3)).extended(var(0))),
            ),
            // …and its own cod, over (Γ₃, cs'', ih''): a = 4, cs = 1, ih = 0.
            cod: Rc::new(
                tel.step_ty.apply_local(
                    &embed(g, 5)
                        .extended(var(4))
                        .extended(var(1))
                        .extended(var(0)),
                ),
            ),
        };
        // Second `cod`, over (Γ₃, ih''): a = 3, cs = 2 (the *real* one, since
        // the first application already consumed it), ih = ih'' = 0.
        let cod2 = tel.step_ty.apply_local(
            &embed(g, 4)
                .extended(var(3))
                .extended(var(2))
                .extended(var(0)),
        );
        let at_cs = crate::spelling::checked_app(
            Rc::new(cased),
            tel.level.clone(),
            tel.mlvl.clone(),
            Rc::new(dom_cs),
            Rc::new(cod1),
            var(1),
        );
        crate::spelling::checked_app(
            Rc::new(at_cs),
            tel.mlvl.clone(),
            tel.mlvl.clone(),
            Rc::new(dom_ih),
            Rc::new(cod2),
            var(0),
        )
    }

    /// The step's case tree (§6.2). Structurally tier 0 §5.2's: right-nested
    /// `Case`, the motive composed with the injection at each depth, no
    /// `Case` at all at the last constructor. What differs is the branch — it
    /// is a pair of λs, not the arm body directly.
    ///
    /// `cx` is Γ₃ plus the `j` binders this recursion has pushed, `motive` is
    /// `P_j` over `(cx, z : R_j)`, `scrut` is the `R_j`-typed scrutinee, and
    /// `d` is how far the spine (scoped in `gamma0`) has to be weakened here.
    #[allow(clippy::too_many_arguments)]
    fn wf_case_tree(
        &self,
        cx: &Cx,
        ind: &Inductive,
        branches: &Branches,
        tel: &Tel,
        dec: Option<usize>,
        j: usize,
        motive: Type,
        plvl: &Level,
        scrut: Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Term> {
        let n = ind.ctors.len();
        if j + 1 == n {
            return self.wf_branch(cx, ind, branches, tel, dec, j, scrut, d, span);
        }
        let ctor_lvl = tel.spine.ctors[j].1.clone();
        let tail_lvl = tel.spine.tails[j].1.clone();
        // Emitted annotations (this `Case`'s two component types, the `Inr`
        // below) take the emission spine; the *binder* types pushed into the
        // elaborator's own context stay inline, so every structural read
        // inside the branch still sees `⟦T⟧` itself (§4's line).
        let ctor_ty = Rc::new(tel.spine_emit.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(tel.spine_emit.tails[j].0.shift_local(d));
        let ctor_ty_in = tel.spine.ctors[j].0.shift_local(d);
        let tail_ty_in = tel.spine.tails[j].0.shift_local(d);
        // case_l: binder `x : ⟦c_j⟧`, body at `P_j[inl x/z]`.
        let mut lcx = cx.clone();
        lcx.push("#scrut".into(), ctor_ty_in, ctor_lvl.clone());
        let case_l = self.wf_branch(
            &lcx,
            ind,
            branches,
            tel,
            dec,
            j,
            Rc::new(Term::Var(LocalVar(0))),
            d + 1,
            span,
        )?;
        // case_r: binder `y : R_{j+1}`; inside it, the next `Case`, whose
        // motive is `P_j` composed with `inr` and weakened past `y`.
        let mut rcx = cx.clone();
        rcx.push("#rest".into(), tail_ty_in, tail_lvl.clone());
        // `inner = P_j[inr z']` over `(cx, y, z')` — **two** binders past `cx`,
        // not one: the `y` this branch binds *and* the inner `Case`'s own
        // motive binder. The substitution's `extra` says 2 and the injection's
        // annotations have to agree, or the spine's field types address `y`
        // where they mean an ambient variable.
        //
        // Invisible at a closed payload type (the annotations then mention no
        // ambient variable at all) and invisible with two constructors (there
        // is no inner `Case`); it took three constructors *and* an open payload
        // — `docs/testing-generated-terms.md` axis 2 — to make the index
        // escape, and then it is a kernel `LevelMismatch`, not a wrong answer.
        let inr = Term::Inr {
            lhs_level: ctor_lvl.clone(),
            rhs_level: tail_lvl.clone(),
            lhs: Rc::new(tel.spine_emit.ctors[j].0.shift_local(d + 2)),
            rhs: Rc::new(tel.spine_emit.tails[j].0.shift_local(d + 2)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let inner = motive.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(inr)));
        let case_r = self.wf_case_tree(
            &rcx,
            ind,
            branches,
            tel,
            dec,
            j + 1,
            inner,
            plvl,
            Rc::new(Term::Var(LocalVar(0))),
            d + 1,
            span,
        )?;
        Ok(Term::Case {
            lhs_level: ctor_lvl,
            rhs_level: tail_lvl,
            motive_level: plvl.clone(),
            lhs: ctor_ty,
            rhs: tail_ty,
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    /// One branch of the step (§6.3): `λ(cs'). λ(ih'). ⟦armᵢ⟧`, with the
    /// surface binders aliased to projections of the label and to `nth` of
    /// the children, and the guard set so that a self-call becomes `ih' ι_t`.
    ///
    /// `value : ⟦cᵢ⟧` is scoped in `cx`, which sits `d` binders past
    /// `gamma0`.
    #[allow(clippy::too_many_arguments)]
    fn wf_branch(
        &self,
        cx: &Cx,
        ind: &Inductive,
        branches: &Branches,
        tel: &Tel,
        dec: Option<usize>,
        i: usize,
        value: Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let m = ctor.arity();
        // The value's full injection into `S`, which is what the telescope's
        // `a` stands for in this branch.
        // The injection's own `Inl`/`Inr` annotations are emitted, so they take
        // the emission spine — the same choice `build_ctor` makes at a value.
        let inj = Rc::new(inject(
            &tel.spine_emit,
            i,
            ind.ctors.len(),
            (*value).clone(),
            d,
        ));
        let (cs_dom, ih_dom, body_ty) = tel.at(&inj, d);

        let mut bcx = cx.clone();
        bcx.push("#cs".into(), cs_dom.clone(), tel.level.clone());
        bcx.push("#ih".into(), ih_dom.clone(), tel.mlvl.clone());
        // In the body: cs' = Var 1, ih' = Var 0, and everything scoped in
        // `cx` has moved two binders out.
        let cs_var = Rc::new(Term::Var(LocalVar(1)));
        let d_body = d + 2;
        // Emission spelling for every annotation this branch writes; the
        // inline one only for the surface binders' *alias types*, which the
        // elaborator reads structurally (a nested `match` on a child binder,
        // `record_of`, `projection`) — §3.1's line, held per reader.
        let d_ty_here = Rc::new(tel.emitted.shift_local(d_body).into_type());
        let d_inline_here = tel.structural.shifted_structure(d_body);
        let ctor_ty_here = tel.spine.ctors[i].0.shift_local(d_body);
        let value_here = Rc::new(value.shift_local(2));
        // This branch's arity. Without a container it is the literal `m`;
        // with one it is `Succ^m(len)` for `len` projected out of the label,
        // which is the *same* term the `Wf`'s arity computes here
        // (docs/container-fields.md §3.3). `Succ`-headed either way, which is
        // what lets `Vec` unfold `m` times and `Fin` admit the `m` literal
        // indices below.
        let container_len = match ctor.container() {
            Some((_, p)) => {
                // `bcx`, not `cx`: both arguments have been shifted by
                // `d_body`, so they live under the two binders just pushed,
                // and `projection` substitutes with the identity of the
                // context it is *given*. Passing `cx` was two entries short.
                //
                // Invisible at a closed instantiation — the constructor
                // encoding's Σ tail then mentions no ambient variable at all,
                // so nothing ever addressed the missing entries. It took a
                // container field at an *open* element type
                // (`Rose<A>`) to make the index escape, which is axis 2 of
                // docs/testing-generated-terms.md, again.
                let (len, _, _) = self.projection(&bcx, &ctor_ty_here, &value_here, p, span)?;
                Some(len)
            }
            None => None,
        };
        let base = match &container_len {
            Some(l) => (**l).clone(),
            None => Term::Zero,
        };
        let len = Rc::new(succ_n(m, &base));

        // The `t`-th child, `nth^l(⟦D⟧; m; cs'; ι_t)`. At a literal `m` this
        // β-reduces to the projections of `cs'` even though `cs'` is a
        // variable, which is what makes an arm binder behave like a field.
        let child = |t: usize| {
            Rc::new(nth_child(
                &tel.level,
                &d_ty_here,
                m,
                t,
                Rc::clone(&cs_var),
                &base,
            ))
        };

        let body = match branches {
            Branches::Custom(f) => f(&bcx, tel, i, &value_here, d_body, &body_ty)?,
            // §7.2: no binders, no guard — just the child, or the default at
            // every other constructor.
            Branches::Child { i: ci, t, default } => {
                if i == *ci {
                    nth_child(&tel.level, &d_ty_here, m, *t, cs_var, &base)
                } else {
                    default.shift_local(d_body)
                }
            }
            // §2 of the list design: the child at a recursive constructor, the
            // outer scrutinee at a base one. `m` is 0 or 1 here — the caller
            // checked [`chain_shaped`] — so "the child" is unambiguous.
            Branches::Tail { default } => {
                if m == 1 {
                    nth_child(&tel.level, &d_ty_here, m, 0, cs_var, &base)
                } else {
                    default.shift_local(d_body)
                }
            }
            Branches::Arms(arms) => {
                let arm = arms[i];
                let mut acx = bcx.clone();
                let ctor_ty = ctor_ty_here.clone();
                let mut children = Vec::with_capacity(m);
                let mut container_ih: Option<ContainerIh> = None;
                let (mut payload_k, mut rec_t) = (0usize, 0usize);
                for (k, name) in arm.binders.iter().map(|p| p.name().to_string()).enumerate() {
                    // The container binder is the *tail* of the children
                    // tuple — one `snd` per preceding plain child, no `nth`
                    // and no index arithmetic (docs/container-fields.md §3.5).
                    if let FieldKind::Container { .. } = ctor.kind[k] {
                        let tail_len = container_len
                            .clone()
                            .expect("a container field has a length");
                        let mut term = Rc::clone(&cs_var);
                        let mut left = m;
                        while left > 0 {
                            left -= 1;
                            let mut rest = (*tail_len).clone();
                            for _ in 0..left {
                                rest = Term::Succ(Rc::new(rest));
                            }
                            term = Rc::new(Term::Snd {
                                fst_level: tel.level.clone(),
                                snd_level: tel.level.clone(),
                                fst_ty: Rc::clone(&d_ty_here),
                                snd_ty: Rc::new(Type::Vec {
                                    level: tel.level.clone(),
                                    elem: Rc::new(tel.emitted.shift_local(d_body + 1).into_type()),
                                    len: Rc::new(rest.shift_local(1)),
                                }),
                                pair: term,
                            });
                        }
                        acx.aliases.push(Rc::new(Alias {
                            skel: None,
                            name: name.clone(),
                            depth: acx.names.len(),
                            term: Rc::clone(&term),
                            ty: Type::Vec {
                                level: tel.level.clone(),
                                elem: Rc::new(d_inline_here.clone()),
                                len: Rc::clone(&tail_len),
                            },
                            level: tel.level.clone(),
                        }));
                        // What a self-call over this binder needs (§4.2). The
                        // motive is strengthened here rather than at the call:
                        // a container maps to a *vector* of results, which
                        // only types when the result is independent of the
                        // child (§4.3).
                        let result = crate::vec::strengthen(&tel.motive, tel.gamma0)
                            .map(|t| t.shift_local(d_body));
                        // Phase 3 (docs/container-proofs.md §5): a dependent
                        // motive that is an equation at a `z`-independent type
                        // still relates the children pointwise. The endpoints
                        // are wrapped as `λ(z : ⟦D⟧). …` so the call site can
                        // shift them like any other term.
                        //
                        // The equation is read through [`Self::motive_head`]:
                        // a *named* statement (`fn Agree(r: Rose) -> Type
                        // { … = … }`) arrives as `El` of a call, and the `Id`
                        // is one δ/β step below it
                        // (docs/record-type-values.md §6).
                        let motive = self.motive_head(tel);
                        let eq = match (&result, &*motive) {
                            (
                                None,
                                Type::Id {
                                    level,
                                    ty,
                                    lhs,
                                    rhs,
                                },
                            ) => crate::vec::strengthen(ty, tel.gamma0).map(|a| {
                                let sigma = crate::embed(tel.gamma0, d_body + 1)
                                    .extended(Rc::new(Term::Var(LocalVar(0))));
                                let lam = |t: &Rc<Term>| {
                                    Rc::new(Term::Lam {
                                        dom_level: tel.level.clone(),
                                        cod_level: level.clone(),
                                        dom: Rc::clone(&d_ty_here),
                                        body: Rc::new(t.apply_local(&sigma)),
                                    })
                                };
                                EqSplit {
                                    level: level.clone(),
                                    ty: a.shift_local(d_body),
                                    lhs: lam(lhs),
                                    rhs: lam(rhs),
                                }
                            }),
                            _ => None,
                        };
                        container_ih = Some(ContainerIh {
                            term,
                            len: tail_len,
                            ih: Rc::new(Term::Var(LocalVar(0))),
                            plain: m,
                            result,
                            eq,
                            // `ih_dom` is scoped where `#ih` is *pushed*, one
                            // binder before the body: `tel.at` builds it at
                            // `d + 1` and the body sits at `d + 2`.
                            ih_ty: ih_dom.shift_local(1),
                            elem: (*d_ty_here).clone(),
                            level: tel.level.clone(),
                            mlvl: tel.mlvl.clone(),
                        });
                        continue;
                    }
                    if ctor.kind[k] == FieldKind::Plain {
                        let c = child(rec_t);
                        // The ih at this index, and the type it lands at: the
                        // eliminator's `cod` binds `i`, so it is
                        // `M[nth(…; i)/z]` one binder deeper, and
                        // instantiating it at `ι_t` gives `M[child/z]` —
                        // which is the child term verbatim.
                        // Everything inside `cod` sits one binder deeper (the
                        // eliminator's `i`), *including the length* — which is
                        // a closed literal without a container and a projection
                        // out of the label with one, so a missing shift here is
                        // invisible until a container constructor carries a
                        // plain child through a proof.
                        let cod = tel
                            .motive
                            .apply_local(&embed(tel.gamma0, d_body + 1).extended(Rc::new(nth(
                                &tel.level,
                                &Rc::new(tel.emitted.shift_local(d_body + 1).into_type()),
                                &Rc::new(len.shift_local(1)),
                                Rc::new(Term::Var(LocalVar(2))),
                                Rc::new(Term::Var(LocalVar(0))),
                            ))));
                        let ih_at = Rc::new(crate::spelling::checked_app(
                            Rc::new(Term::Var(LocalVar(0))),
                            Level::Zero,
                            tel.mlvl.clone(),
                            Rc::new(Type::Fin {
                                len: Rc::clone(&len),
                            }),
                            Rc::new(cod),
                            Rc::new(fin_index(rec_t, m, &base)),
                        ));
                        let ih_ty = tel
                            .motive
                            .apply_local(&embed(tel.gamma0, d_body).extended(Rc::clone(&c)));
                        acx.aliases.push(Rc::new(Alias {
                            skel: None,
                            name: name.clone(),
                            depth: acx.names.len(),
                            term: Rc::clone(&c),
                            ty: d_inline_here.clone(),
                            level: tel.level.clone(),
                        }));
                        children.push((c, ih_at, ih_ty, tel.mlvl.clone()));
                        rec_t += 1;
                    } else {
                        let (proj, ty, level) =
                            self.projection(&acx, &ctor_ty, &value_here, payload_k, span)?;
                        acx.aliases.push(Rc::new(Alias {
                            skel: None,
                            name: name.clone(),
                            depth: acx.names.len(),
                            term: proj,
                            ty,
                            level,
                        }));
                        payload_k += 1;
                    }
                }
                // A self-call in this arm is the ih (§6.4) — but only if the
                // `match` descends on one of the declaration's own
                // parameters. If it does not, an enclosing arm's guard, if
                // any, still stands.
                let plain_guard = |acx: &Cx, cov: Option<Rc<WfCov>>, children| {
                    dec.map(|dec| {
                        Rc::new(Guard {
                            dec,
                            kind: GuardKind::Wf {
                                depth: acx.names.len(),
                                children,
                                container: container_ih.clone(),
                                cov,
                            },
                            rebind: None,
                            generalized: crate::generalize::guard_gen(cx, dec, Some(span)),
                        })
                    })
                    .or_else(|| cx.guard.clone())
                };
                match &tel.rec {
                    TelRec::None => {
                        acx.guard = plain_guard(&acx, None, children);
                        self.elab_check(&acx, &arm.body, &body_ty, &tel.mlvl)?
                    }
                    // The window (§3): the arm the writer wrote, tupled with
                    // the window slid by one.
                    TelRec::Cov { d, step, plain } => {
                        let ChainStep::Tail(tail) = step else {
                            return err("internal: a `Wf` window without `tail_D`", span);
                        };
                        // The arm's own value, spelled as the constructor
                        // *rebuilt around its child* rather than as the
                        // `sup_f(ℓ; cs')` the telescope states its step at.
                        // The two are convertible — `cs'` is a one-element
                        // `Vec`, and η gives `(nth cs' ι₀, ⟨⟩) ≡ cs'` — and
                        // the rebuilt spelling is the one with the child as a
                        // *subterm*, which is what lets a nested `match` on it
                        // refine this goal the way `Succ k` does for `Nat`
                        // (`docs/list-course-of-values-design.md` §7.4).
                        //
                        // The components are annotated at it, where the kernel
                        // checks them; a shifted component differs from its
                        // annotation only by `tail_D(Cᵢ(p, t)) ⇝ t`, which
                        // conversion does.
                        let here = children.first().cloned();
                        let value = match &here {
                            Some((child, ..)) => tel.rebuilt_here(&inj, d_body, child),
                            None => tel.value_at(&inj, d_body),
                        };
                        let comps = cov_comps(tel.gamma0, step, plain, *d, d_body, &value);
                        match here {
                            Some((child, ih, ..)) => {
                                // An anchor is a λ so that it shifts like a
                                // closed term; its body mentions this arm's
                                // payload binders, which are not ambient.
                                let lam = |body: Term| Term::Lam {
                                    dom_level: tel.level.clone(),
                                    cod_level: tel.level.clone(),
                                    dom: Rc::new(
                                        tel.emitted.shift_local(d_body).into_type(),
                                    ),
                                    body: Rc::new(body),
                                };
                                let at_child =
                                    cov_comps(tel.gamma0, step, plain, *d, d_body, &child);
                                let window = Rc::new(WfCov {
                                    chain: vec![Rc::clone(&child)],
                                    tuple: (*ih).clone(),
                                    comps: at_child.clone(),
                                    mlvl: tel.mlvl.clone(),
                                    motive: Rc::clone(plain),
                                    gamma: tel.gamma0.clone(),
                                    tail: Rc::clone(tail),
                                    // The recursion's own `match`: the window
                                    // is anchored at this arm's child, which
                                    // is the chain's end, so the window anchor
                                    // is the identity — while the *goal* is
                                    // this arm's own constructor, since a
                                    // nested `match` on the child refines the
                                    // arm's obligation to `M[Cᵢ(p, y)]`.
                                    window: Rc::new(lam(Term::Var(LocalVar(0)))),
                                    // One binder past the branch — the
                                    // anchor's own `y` — and no convoy binder
                                    // here, which is where `rebuilt_at` sits.
                                    goal: Rc::new(lam(tel.supf_over(
                                        &inj,
                                        d_body,
                                        d_body + 1,
                                        Rc::new(Term::Var(LocalVar(0))),
                                    ))),
                                });
                                acx.guard = plain_guard(&acx, Some(window), children);
                                let body =
                                    self.elab_check(&acx, &arm.body, &comps[0], &tel.mlvl)?;
                                let mut vals = vec![body];
                                vals.extend((0..*d - 1).map(|i| {
                                    cov_proj(&at_child, &tel.mlvl, (*ih).clone(), i)
                                }));
                                cov_tuple(&comps, &tel.mlvl, vals)
                            }
                            // A base constructor emits its own value `d`
                            // times (§3): `tail_D` there is the scrutinee, so
                            // all `d` components sit at the same type, and
                            // nothing can read the copies — a call at depth
                            // `i` is only in scope inside `i` nested
                            // recursive arms.
                            None => {
                                acx.guard = plain_guard(&acx, None, children);
                                let body =
                                    self.elab_check(&acx, &arm.body, &comps[0], &tel.mlvl)?;
                                cov_tuple(&comps, &tel.mlvl, vec![body; *d])
                            }
                        }
                    }
                    // The convoy (§4): the window arrives as an argument, and
                    // its type at the *rebuilt* constructor is what makes the
                    // component one below this arm's scrutinee reduce to the
                    // motive at the child the arm binds.
                    TelRec::Convoy { convoy, body_lvl } => {
                        let value = tel.value_at(&inj, d_body);
                        let at = convoy.window(tel.gamma0, d_body, value);
                        let comps = cov_comps(
                            tel.gamma0,
                            &convoy.step,
                            &convoy.motive,
                            convoy.d,
                            d_body,
                            &at,
                        );
                        let dom = cov_ty(&comps, &convoy.lvl);
                        let Type::Pi { cod, .. } = &body_ty else {
                            return err("internal: a convoyed arm is not a Π", span);
                        };
                        let mut ccx = acx.clone();
                        ccx.push("#cov".into(), dom.clone(), convoy.lvl.clone());
                        // Past the convoy binder itself.
                        let up = d_body + 1;
                        let mut chain: Vec<Rc<Term>> = convoy
                            .chain
                            .iter()
                            .map(|t| Rc::new(t.shift_local(up)))
                            .collect();
                        let elem = Rc::new(tel.emitted.shift_local(up).into_type());
                        // Both anchors grow by *this* arm's constructor: a
                        // nesting one deeper scrutinizes the child, and what
                        // stood at its scrutinee now stands at
                        // `Cᵢ(payload, y)`. A base arm extends the chain by
                        // nothing and so composes with nothing — it is
                        // convoyed all the same, since its own components sit
                        // at `tail_D^i` of its own value and a call at the
                        // chain's head belongs there too.
                        let (window_anchor, goal_anchor) = match children.first() {
                            Some((child, ..)) => {
                                chain.push(Rc::new(child.shift_local(1)));
                                let rebuilt = tel.rebuilt_at(&inj, d_body);
                                (
                                    convoy.window(tel.gamma0, d_body + 2, rebuilt.clone()),
                                    convoy.goal(tel.gamma0, d_body + 2, rebuilt),
                                )
                            }
                            None => {
                                let y = Term::Var(LocalVar(0));
                                (
                                    convoy.window(tel.gamma0, d_body + 2, y.clone()),
                                    convoy.goal(tel.gamma0, d_body + 2, y),
                                )
                            }
                        };
                        let window = Rc::new(WfCov {
                            chain,
                            tuple: Term::Var(LocalVar(0)),
                            comps: comps.iter().map(|c| c.shift_local(1)).collect(),
                            mlvl: convoy.lvl.clone(),
                            motive: Rc::clone(&convoy.outer_motive),
                            gamma: convoy.gamma.clone(),
                            tail: Rc::clone(&convoy.outer_tail),
                            window: Rc::new(Term::Lam {
                                dom_level: tel.level.clone(),
                                cod_level: tel.level.clone(),
                                dom: Rc::clone(&elem),
                                body: Rc::new(window_anchor),
                            }),
                            goal: Rc::new(Term::Lam {
                                dom_level: tel.level.clone(),
                                cod_level: tel.level.clone(),
                                dom: Rc::clone(&elem),
                                body: Rc::new(goal_anchor),
                            }),
                        });
                        ccx.guard = Some(Rc::new(Guard {
                            dec: convoy.dec,
                            kind: GuardKind::Wf {
                                depth: ccx.names.len(),
                                // A convoyed `match` descends on nothing of
                                // its own: the ih a self-call takes is the
                                // window's, not this eliminator's.
                                children: Vec::new(),
                                container: None,
                                cov: Some(window),
                            },
                            rebind: None,
                            generalized: convoy.generalized.clone(),
                        }));
                        let body = self.elab_check(&ccx, &arm.body, cod, body_lvl)?;
                        Term::Lam {
                            dom_level: convoy.lvl.clone(),
                            cod_level: body_lvl.clone(),
                            dom: Rc::new(dom),
                            body: Rc::new(body),
                        }
                    }
                }
            }
        };
        Ok(Term::Lam {
            dom_level: tel.level.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(cs_dom),
            body: Rc::new(Term::Lam {
                dom_level: tel.mlvl.clone(),
                cod_level: tel.mlvl.clone(),
                dom: Rc::new(ih_dom),
                body: Rc::new(body),
            }),
        })
    }
}

impl Elaborator {
    // -- no-confusion (§7) --------------------------------------------------

    /// `elim_Wf` at a **constant** motive, with a constant-motive case tree on
    /// the tag as its step (§7). Both halves of no-confusion are this: the
    /// disjointness predicate is it at the motive `Ty 0`, and a field
    /// projection is it at the motive "that field's type". Neither is an
    /// inductive argument, so the step ignores `ih` entirely.
    ///
    /// Scoping follows tier 0 §6's convention, which is worth stating because
    /// it is mixed on purpose: `spine`, `d_ty` and the `ConstBody` payloads
    /// are scoped in the *base* context the caller read them back in, `d0`
    /// counts the binders pushed since (2, inside a `J` motive), and `motive`
    /// and `scrut` are scoped in `cx` — here and now.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn const_elim_wf(
        &self,
        cx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        spine: &Spine,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &ConstBody,
        d0: u32,
        span: Span,
    ) -> R<Term> {
        let Type::Wf {
            level,
            shape,
            arity,
        } = d_ty.shift_local(d0)
        else {
            return err(
                "internal: a recursive declaration did not lower to a `Wf`",
                span,
            );
        };
        // The motive binds `z` and ignores it; the telescope needs it anyway,
        // since `ih_ty` and `step_ty` are stated in terms of it.
        let under_z = Rc::new(motive.shift_local(1));
        let (cs_ty, ih_ty, _) =
            wf_step_telescope(&cx.gamma, &level, mlvl, &shape, &arity, &under_z);
        let mut cx3 = cx.clone();
        cx3.push("#a".into(), (*shape).clone(), level.clone());
        cx3.push("#cs".into(), cs_ty, level.clone());
        cx3.push("#ih".into(), ih_ty, mlvl.clone());
        let step = self.const_case_tree(
            &cx3,
            spine,
            ind.ctors.len(),
            &motive.shift_local(3),
            mlvl,
            Rc::new(Term::Var(LocalVar(2))),
            body,
            0,
            d0 + 3,
            span,
        )?;
        Ok(Term::ElimWf {
            level,
            motive_level: mlvl.clone(),
            shape,
            arity,
            motive: under_z,
            step: Rc::new(step),
            scrut,
        })
    }
}

/// `nth^l(⟦D⟧; m; cs; ι_t)` — the `t`-th of `m` children of `cs` (§6.3).
/// Shared by the `match` arms, which bind it as an alias, and by
/// injectivity, which projects with it.
/// The `t`-th plain child, out of a children tuple whose length is
/// `Succ^m(base)`.
///
/// `base` is `Zero` for a constructor with no container field — recovering
/// tier 1's literal `m` exactly — and the container's length term otherwise
/// (docs/container-fields.md §3.3). Either way the length is `Succ`-headed
/// `m` times, which is all `nth` and `Fin` need in order to reduce down to
/// the `t`-th projection.
pub(crate) fn nth_child(
    level: &Level,
    d_ty: &Rc<Type>,
    m: usize,
    t: usize,
    cs: Rc<Term>,
    base: &Term,
) -> Term {
    nth(
        level,
        d_ty,
        &Rc::new(succ_n(m, base)),
        cs,
        Rc::new(fin_index(t, m, base)),
    )
}

/// `Succ^k(base)`.
fn succ_n(k: usize, base: &Term) -> Term {
    let mut acc = base.clone();
    for _ in 0..k {
        acc = Term::Succ(Rc::new(acc));
    }
    acc
}

/// The index `t` of `Fin(Succ^m(base))`: `inr^t (inl ⟨⟩)` (§6.3). Each tail is
/// annotated with `Fin` itself rather than its unfolded sum — `Fin(S k) ⇝
/// Unit⁰ + Fin(k)`, so the kernel converts the two, and the folded form is
/// what a goal reads back as.
pub(crate) fn fin_index(t: usize, m: usize, base: &Term) -> Term {
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let fin = |k: usize| {
        Rc::new(Type::Fin {
            len: Rc::new(succ_n(k, base)),
        })
    };
    let mut v = Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: unit(),
        rhs: fin(m - t - 1),
        val: Rc::new(Term::Triv { level: Level::Zero }),
    };
    for k in (0..t).rev() {
        v = Term::Inr {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: fin(m - k - 1),
            val: Rc::new(v),
        };
    }
    v
}

// ---------------------------------------------------------------------------

#[cfg(test)]
mod tycode {
    //! The tier-1 `D#tycode` spelling
    //! (`docs/family-type-code-defs-design.md`, 2026-08-12 extension;
    //! `issues/wf-field-conversion-cost.md`).
    //!
    //! Two obligations, and they are different in kind. The **emission** side
    //! is checked by elaborating real source: a wrong spelling in an
    //! annotation slot is a kernel rejection at the declaration's own gate, so
    //! "it elaborates" *is* the assertion, and the four axes of
    //! `docs/testing-generated-terms.md` are what make that assertion cover
    //! anything (a literal and a neutral scrutinee, an open element type, a
    //! checking position, a negative control). The **recognition** side is
    //! checked structurally, with `forded.rs mod fingerprint`'s look-alike
    //! discipline: a reference must stand for the declaration it names and for
    //! nothing else, in both directions.

    use super::*;
    use crate::gendefs::GenDef;
    use heather_kernel::term::{CtxBase, GlobalBinding, GlobalVar, LocalSubst, SubstTail};

    const SPAN: Span = Span { start: 0, end: 0 };

    /// Two tier-1 declarations that are structurally identical apart from
    /// their nominal tags (the look-alike pair, `mod fingerprint`'s
    /// construction), one non-recursive declaration — whose lowering is a bare
    /// sum-of-Σs and which gets a code all the same — and one *parameterized*
    /// declaration, which must not.
    ///
    /// The records cover §13's four corners of the projection boundary:
    /// `Cell<A, B>` telescoped and non-dependent (the `MachineState<M>`
    /// shape), `Dep<A>(n)` telescoped and dependent, `Plain` closed and
    /// non-dependent (which keeps the inline walk) and `DepC` closed and
    /// dependent (which does not).
    const SRC: &str = "
inductive T { T0, T1(x: Nat, r: T), T2(y: Nat, r: T) }
inductive U { U0, U1(x: Nat, r: U), U2(y: Nat, r: U) }
inductive Flat { FA, FB(n: Nat), FC(m: Nat, k: Nat) }
inductive Flat2 { GA, GB(n: Nat), GC(m: Nat, k: Nat) }
inductive Box<A> { BNil, BCons(a: A, r: Box<A>) }
inductive Two<A, B> { MkTwo(a: A, b: B) }
inductive Box2<A> { CNil, CCons(a: A, r: Box2<A>) }
record BV(n: Nat) { bits: [Nat; n] }
record Mixed<A>(n: Nat) { a: A, bits: [Nat; n] }
record Cell<A, B> { l: A, r: B }
record Dep<A>(n: Nat) { k: Nat, same: k = n, a: A }
record Plain { p: Nat, q: Nat }
record DepC { m: Nat, eq: m = m }
";

    struct Env {
        el: Elaborator,
        cx: Cx,
    }

    fn env() -> Env {
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(SRC).expect("the declarations elaborate");
        Env {
            el,
            cx: Cx::empty(),
        }
    }

    impl Env {
        fn ind(&self, name: &str) -> Rc<Inductive> {
            Rc::clone(
                self.el
                    .types
                    .inductive(&crate::names::qkey("main", name))
                    .unwrap_or_else(|| panic!("`{name}` was declared")),
            )
        }
        fn lowered(&self, name: &str) -> (Type, Level) {
            self.el
                .lower_instance(&self.cx, &self.ind(name), &[], &[], SPAN)
                .expect("the declaration lowers")
        }
    }

    #[test]
    fn telescope_roles_validate_structure_and_preserve_emission_when_shifted() {
        let e = env();
        let (inline, _) = e.lowered("T");
        let structural = StructuralWf::new(&inline).expect("a recursive lowering");
        let emitted = structural.annotation(&e.el, &e.cx);
        let Type::El { tm, .. } = emitted.as_type() else { panic!("named annotation") };
        assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("T").tag)));
        assert!(StructuralWf::new(&Type::Nat).is_none());
        assert!(StructuralWf::new(emitted.as_type()).is_none(),
            "a named code cannot enter the structural boundary without decoding");
        assert_eq!(emitted.shift_local(1).into_type(),
            e.el.annotation_type(&e.cx, &inline, 1));
        assert_eq!(structural.shifted_structure(1), inline.shift_local(1));
    }

    // -- registration boundary ----------------------------------------------

    #[test]
    fn a_closed_declaration_gets_a_code_and_a_parameterized_one_does_not() {
        let e = env();
        for name in ["T", "U", "Flat"] {
            let tag = e.ind(name).tag;
            assert!(
                e.el.gen_ref(&e.cx, GenDef::TyCode(tag)).is_some(),
                "`{name}` should have a `#tycode`"
            );
        }
        // §14.12's boundary, verbatim: `⟦Box<A>⟧` is monomorphized per
        // instantiation, so there is no one closed type to name.
        assert!(
            e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind("Box").tag))
                .is_none()
        );
    }

    #[test]
    fn the_reference_is_el_of_the_declarations_own_code() {
        let e = env();
        let (t_ty, l) = e.lowered("T");
        let r =
            e.el.respell_ty(&e.cx, &t_ty)
                .expect("T's lowering respells");
        let Type::El { level, tm } = &r else {
            panic!("the spelling is `El` of a code")
        };
        assert_eq!(*level, l);
        assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("T").tag)));
        // Idempotent: `tag_of` goes through `decoded`, which leaves an `El` of
        // a neutral code alone, so a reference does not respell again.
        assert!(e.el.respell_ty(&e.cx, &r).is_none());
        // Conservativity (design §1.3): δ + decode of the reference is the
        // inline type, so the two convert.
        assert!(e.el.conv_types(&e.cx, &r, &t_ty, &l));
        assert!(e.el.conv_types(&e.cx, &t_ty, &r, &l));
    }

    // -- the look-alike negatives (design §4, §9) ---------------------------

    #[test]
    fn a_type_the_tag_read_routes_to_but_which_is_not_the_lowering_declines() {
        let e = env();
        // This is the guard the registry's inline copy exists for. `tag_of`
        // walks a `Sum` into its left summand to find a tag, so a type built
        // out of **T's first constructor** and something else names `T` — and
        // it is not `⟦T⟧`. Without the structural comparison the emission
        // sites would spell it `El (T#tycode^δ)`, which decodes to a
        // different type: not a rejection, a *wrong annotation*, which is the
        // failure mode this module's doctrine exists to prevent.
        let (t_ty, l) = e.lowered("T");
        let Type::Wf { shape, .. } = &t_ty else {
            panic!("T is recursive")
        };
        let Type::Sum { lhs, lhs_level, .. } = &**shape else {
            panic!("a tier-1 shape is a sum-of-Σs")
        };
        let forgery = Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: Level::Zero,
            lhs: Rc::clone(lhs),
            rhs: Rc::new(Type::Unit { level: Level::Zero }),
        };
        assert_eq!(e.el.tag_of(&forgery).map(|i| i.tag), Some(e.ind("T").tag));
        assert!(e.el.respell_ty(&e.cx, &forgery).is_none());
        // …and the same read keyed by hand at the tag declines too, which is
        // the property `respell_ty` inherits rather than adds.
        assert!(e.el.closed_type_ref(&e.cx, e.ind("T").tag, &forgery).is_none());
        let _ = l;
    }

    #[test]
    fn el_of_the_wrong_declarations_code_is_not_this_declaration() {
        let e = env();
        // `U`'s code — a real registered definition of a real declaration
        // that differs from `T` only in its tags — offered where `T`'s
        // lowering is expected.
        let (_, l) = e.lowered("T");
        let u_code =
            e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind("U").tag))
                .expect("U has a code");
        let forged = Type::El {
            level: l,
            tm: Rc::new(u_code),
        };
        // Neither by tag…
        assert!(e.el.closed_type_ref(&e.cx, e.ind("T").tag, &forged).is_none());
        // …nor by the structural read, which does not follow a neutral code.
        assert!(e.el.respell_ty(&e.cx, &forged).is_none());
    }

    #[test]
    fn el_of_a_byte_identical_user_global_is_not_the_declaration() {
        let mut e = env();
        // Identity is the Ψ index, not the body: a bodied global whose
        // statement, layer and body are byte-identical to `T#tycode`'s, pushed
        // outside the registry the way a user `fn` is, resolves to no
        // `GenDef`.
        let (t_ty, l) = e.lowered("T");
        let code = crate::code::code_of(&t_ty).expect("T's lowering has a code");
        e.el.psi.push(GlobalBinding::defined_tm(
            LocalCtx::nil(),
            heather_kernel::layer::Layer::Code,
            Rc::new(Type::Ty(l.clone())),
            Level::succ(l.clone()),
            Rc::new(code),
        ));
        e.el.refresh_delta_psi();
        let dup = Term::GlobalTm {
            var: GlobalVar(e.el.global_padding()),
            subst: LocalSubst {
                tail: SubstTail::Empty {
                    len: 0,
                    base: CtxBase::Nil,
                },
                terms: vec![],
            },
        };
        assert!(
            e.el.gen_def_of(GlobalVar(e.el.global_padding()))
                .is_none()
        );
        let forged = Type::El {
            level: l,
            tm: Rc::new(dup),
        };
        assert!(e.el.closed_type_ref(&e.cx, e.ind("T").tag, &forged).is_none());
        assert!(e.el.respell_ty(&e.cx, &forged).is_none());
    }

    // -- emission: the four axes --------------------------------------------

    /// A `match` really does emit the reference — otherwise every "it
    /// elaborates" below would be vacuous.
    #[test]
    fn a_tier1_match_emits_the_reference_in_its_motive() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source(
            "fn drop2(t: T) -> T { match t { T0 => T0, T1(x, r) => r, T2(y, r) => r } }",
        )
        .expect("elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` is a bodied term binding")
        };
        let Term::Lam { body, .. } = &**body else {
            panic!("one parameter, one λ")
        };
        let Term::ElimWf { motive, .. } = &**body else {
            panic!("tier 1 lowers to `elim_Wf`")
        };
        let Type::El { tm, .. } = &**motive else {
            panic!("the motive is the reference, not the inline `Wf`")
        };
        // `GlobalVar` counts from the end of Ψ, so the reference the body
        // carries was minted against the Ψ *before* the declaration's own
        // binding; re-key it into today's Ψ before asking the registry, or the
        // nominal test silently reads one binding over.
        let grew = (e.el.psi.bindings.len() - before) as u32;
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::TyCode(e.ind("T").tag)));
    }

    /// Axes 1–4 on the tier-1 path, one source: a **neutral** scrutinee (the
    /// parameter `t`) and a **literal** one (`T1(1, T0)`), a **checking**
    /// position (`h`'s annotated result and the `refl`), and the computation
    /// pinned rather than merely built.
    #[test]
    fn the_four_axes_on_a_recursive_declaration() {
        let mut e = env();
        e.el
            .elab_source(
                "
fn depth(t: T) -> Nat { match t { T0 => 0, T1(x, r) => Succ(depth(r)), T2(y, r) => Succ(depth(r)) } }
fn peel(t: T) -> T { match t { T0 => T0, T1(x, r) => r, T2(y, r) => T1(y, r) } }
fn lit() -> T { match T1(1, T0) { T0 => T0, T1(x, r) => r, T2(y, r) => r } }
theorem lit_is_t0(): lit() = T0 { refl }
theorem peel_computes(): peel(T2(3, T1(1, T0))) = T1(3, T1(1, T0)) { refl }
theorem depth_computes(): depth(T1(1, T2(2, T0))) = 2 { refl }
",
            )
            .expect("the reference-spelled annotations check and compute");
    }

    /// Axis 2, the one that hid three of the five live defects: an **open**
    /// element type. `Box<A>` has no code (§14.12), so this is also the
    /// coexistence control — a parameterized declaration's `match` still
    /// elaborates with everything inline, beside declarations that do have
    /// codes.
    #[test]
    fn a_parameterized_declaration_still_lowers_inline() {
        let mut e = env();
        e.el.elab_source(
            "
fn blen<A>(b: Box<A>) -> Nat { match b { BNil => 0, BCons(a, r) => Succ(blen(r)) } }
fn bnat(b: Box<Nat>) -> Nat { match b { BNil => 7, BCons(a, r) => a } }
theorem bnat_computes(): bnat(BCons(4, BNil)) = 4 { refl }
",
        )
        .expect("a parameterized declaration keeps its inline lowering");
        assert!(
            e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind("Box").tag))
                .is_none()
        );
    }

    /// The tier-0 twin: a **non-recursive** declaration's `match` goes through
    /// `case_tree`, whose one Θ(arms)-copied whole type is the motive. Both
    /// scrutinee kinds, and a mixed pair — a recursive scrutinee at a
    /// non-recursive motive, which is the shape (`Ir -> CertOut`) that made
    /// the non-recursive registration worth having.
    #[test]
    fn the_tier0_motive_respell_checks_and_computes() {
        let mut e = env();
        e.el.elab_source(
            "
fn fnext(f: Flat) -> Flat { match f { FA => FB(1), FB(n) => FC(n, n), FC(m, k) => FA } }
fn tflat(t: T) -> Flat { match t { T0 => FA, T1(x, r) => FB(x), T2(y, r) => FC(y, y) } }
theorem fnext_computes(): fnext(FB(2)) = FC(2, 2) { refl }
theorem tflat_computes(): tflat(T1(5, T0)) = FB(5) { refl }
theorem tflat_neutral(): tflat(T0) = FA { refl }
",
        )
        .expect("the tier-0 motive respell checks and computes");
    }

    /// The Ψ-numbering regression this round found: a `meta fn`'s `Ctx`
    /// binders extend Ψ, and `gen_ref` used not to offset by them the way
    /// `resolve` always has. Nothing emitted a generated-definition reference
    /// from inside a meta body until the motive respell did, and the symptom
    /// was `WrongGlobalBinding` naming the context binder.
    #[test]
    fn a_reference_emitted_inside_a_meta_body_is_numbered_past_the_ctx_binder() {
        let mut e = env();
        e.el.elab_source(
            "meta fn mwalk(g: Ctx, t: T) -> Nat \
                 { match t { T0 => 0, T1(x, r) => 1, T2(y, r) => 2 } }",
        )
        .expect("a meta body's `match` on a coded declaration checks at layer m");
    }

    // -- the component respell (docs/annotation-component-respell-design.md) --

    /// `respell_ty_deep` replaces exactly the components that are registered
    /// lowerings, at the right depths: a `Π` over two coded declarations
    /// respells both sides, the binder-crossing side with its substitution
    /// tail one longer.
    #[test]
    fn the_deep_respell_replaces_components_at_their_depths() {
        let e = env();
        let (t_ty, tl) = e.lowered("T");
        let (f_ty, fl) = e.lowered("Flat");
        let pi = Type::Pi {
            dom_level: tl.clone(),
            cod_level: fl.clone(),
            dom: Rc::new(t_ty.clone()),
            cod: Rc::new(f_ty.clone()),
        };
        let r =
            e.el.respell_ty_deep(&e.cx, &pi, 0)
                .expect("both components respell");
        let Type::Pi { dom, cod, .. } = &r else {
            panic!("the Π shell survives")
        };
        let Type::El { tm: dtm, .. } = &**dom else {
            panic!("dom is a reference")
        };
        let Type::El { tm: ctm, .. } = &**cod else {
            panic!("cod is a reference")
        };
        assert!(e.el.is_gen_ref(dtm, GenDef::TyCode(e.ind("T").tag)));
        assert!(e.el.is_gen_ref(ctm, GenDef::TyCode(e.ind("Flat").tag)));
        // The respelled Π still converts with the inline one — component
        // respelling is a spelling change, both directions.
        let lvl = Level::max(tl, fl);
        assert!(e.el.conv_types(&e.cx, &r, &pi, &lvl));
        assert!(e.el.conv_types(&e.cx, &pi, &r, &lvl));
        // Idempotent, like the whole-type respell.
        assert!(e.el.respell_ty_deep(&e.cx, &r, 0).is_none());
        // And a type with no registered component answers `None` — the
        // caller keeps its original.
        assert!(e.el.respell_ty_deep(&e.cx, &Type::Nat, 0).is_none());
    }

    /// The statement-side respell, pinned structurally rather than assumed: a
    /// declared `fn`'s Ψ statement carries the reference in its `Π` dom, and
    /// a *call* to it then emits an `App` whose `dom` annotation is that
    /// reference — the cascade that makes per-application respelling
    /// unnecessary (design §2.1).
    #[test]
    fn a_statement_respells_and_calls_inherit_it() {
        let mut e = env();
        e.el.elab_source("fn tid(t: T) -> T { t }")
            .expect("elaborates");
        let GlobalBinding::Tm { ty, .. } = e.el.psi.bindings.last().expect("a binding") else {
            panic!("a `fn` is a term binding")
        };
        let Type::Pi { dom, cod, .. } = &**ty else {
            panic!("one parameter, one Π")
        };
        let Type::El { tm, .. } = &**dom else {
            panic!("the statement's dom is the reference, not the inline `Wf`")
        };
        assert!(e.el.is_gen_ref(&tm.shift_global(1), GenDef::TyCode(e.ind("T").tag)));
        let Type::El { .. } = &**cod else {
            panic!("the result respells too")
        };
        // The cascade: a later declaration's call reads its domain off that
        // statement. Since `docs/app-by-head-type-design.md` it reads it at
        // check time and writes none: the call is `app@(tid; t)`, so no
        // annotation exists that could carry an inline copy of `T`.
        e.el.elab_source("fn call_it(t: T) -> T { tid(t) }")
            .expect("elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Lam { body, .. } = &**body else {
            panic!("one λ")
        };
        let Term::AppAt { fun, .. } = &**body else {
            panic!("the body is the call, written `app@`")
        };
        assert!(matches!(&**fun, Term::GlobalTm { .. }), "the head is `tid`");
    }

    /// A declaration with a coded declaration as a **field type**: the
    /// projection chains and the value tuple's `Pair`/`Inl`/`Inr` annotations
    /// carry `⟦T⟧` and now respell it (design §2.2/§2.3). Literal and neutral
    /// scrutinees, a checking position, computation pinned by `refl`, and the
    /// negative control on the same path.
    #[test]
    fn field_projections_and_values_respell_and_still_compute() {
        let mut e = env();
        e.el.elab_source(
            "
inductive P { MkP(t: T, n: Nat), NoP }
fn getp(p: P) -> T { match p { MkP(t, n) => t, NoP => T0 } }
fn wrap(t: T) -> P { MkP(t, 7) }
theorem getp_computes(): getp(MkP(T1(1, T0), 2)) = T1(1, T0) { refl }
theorem roundtrip(t: T): getp(wrap(t)) = t { refl }
",
        )
        .expect("field projections and values respell and still compute");
        let r =
            e.el.elab_source("theorem wrong_field(): getp(MkP(T1(1, T0), 2)) = T0 { refl }");
        assert!(r.is_err(), "a false field equation must still be refused");
    }

    /// Axis 2 crossed with the respell: a **parameterized** container at a
    /// coded instantiation. `Box<T>` itself has no code (§14.12), but its
    /// monomorphized lowering *contains* `⟦T⟧`, which the deep respell names
    /// component-wise — the `Wf`-shape recursion arm's one live case.
    #[test]
    fn a_monomorphized_container_of_a_coded_declaration_respells_inside() {
        let mut e = env();
        e.el.elab_source(
            "
fn bt_head(b: Box<T>) -> T { match b { BNil => T0, BCons(a, r) => a } }
theorem bt_computes(): bt_head(BCons(T1(3, T0), BNil)) = T1(3, T0) { refl }
",
        )
        .expect("a Box<T> match elaborates with component references");
    }

    /// The regression this round's respell surfaced (and whose fix lives in
    /// the kernel — `conv.rs tm_w`'s type-δ stage, pinned kernel-side in
    /// `crates/kernel/tests/definitions.rs`): an auto-`refl` hole (`{}`)
    /// converts two canonical values **at** `Id`'s type component, which a
    /// respelled statement now spells `El (T#tycode^δ)`. Before the fix the
    /// δ-stuck type sent both literals into the neutral-type arm and the
    /// hole went unsolved — every `{}` over a coded declaration's result
    /// type, `lib/list_algos.hthr`'s shape.
    #[test]
    fn an_auto_refl_hole_solves_at_a_respelled_result_type() {
        let mut e = env();
        e.el.elab_source(
            "
fn tz(t: T) -> T { T0 }
theorem tz_computes(t: T): tz(t) = T0 { {} }
",
        )
        .expect("a `{}` hole converts at the `El`-spelled Id component");
    }

    /// The negative control the four axes ask for: a wrong arm is still a
    /// failed `refl`. A spelling change must not make anything *more*
    /// convertible — δ + decode is conservative, not permissive.
    #[test]
    fn a_wrong_computation_is_still_refused() {
        let mut e = env();
        let r = e.el.elab_source(
            "
fn peel(t: T) -> T { match t { T0 => T0, T1(x, r) => r, T2(y, r) => T1(y, r) } }
theorem wrong(): peel(T1(1, T0)) = T1(1, T0) { refl }
",
        );
        assert!(r.is_err(), "a false equation must still be refused");
    }

    // -- the Wf slot pair (docs/wf-shape-code-design.md) --------------------

    /// The registration boundary of the pair, which is narrower than
    /// `TyCode`'s in one direction: a **non-recursive** declaration lowers to
    /// a bare sum-of-Σs and has no slots to name at all.
    #[test]
    fn a_recursive_declaration_gets_a_shape_and_an_arity_and_a_flat_one_does_not() {
        let e = env();
        for name in ["T", "U"] {
            let tag = e.ind(name).tag;
            assert!(
                e.el.gen_ref(&e.cx, GenDef::ShapeCode(tag)).is_some(),
                "`{name}` should have a `#shape`"
            );
            assert!(
                e.el.gen_ref(&e.cx, GenDef::ArityFn(tag)).is_some(),
                "`{name}` should have a `#arity`"
            );
        }
        // No `Wf`, no slots — `Flat` keeps its `#tycode` and nothing else.
        assert!(
            e.el.gen_ref(&e.cx, GenDef::ShapeCode(e.ind("Flat").tag))
                .is_none()
        );
        assert!(
            e.el.gen_ref(&e.cx, GenDef::ArityFn(e.ind("Flat").tag))
                .is_none()
        );
        // …and the monomorphization boundary is `TyCode`'s, inherited.
        assert!(
            e.el.gen_ref(&e.cx, GenDef::ShapeCode(e.ind("Box").tag))
                .is_none()
        );
    }

    /// What the two references *are*, structurally, and that the `Wf` rebuilt
    /// from them is the declaration's lowering (design §6's conservativity, at
    /// the slots rather than the whole type).
    #[test]
    fn the_slot_references_are_the_shape_code_and_an_application_of_the_arity() {
        let e = env();
        let (t_ty, l) = e.lowered("T");
        let Type::Wf { shape, arity, .. } = &t_ty else {
            panic!("T is recursive")
        };
        let (sref, aref) =
            e.el.wf_slot_refs(&e.cx, shape, arity)
                .expect("T's slots respell");
        let Type::El { tm, .. } = &sref else {
            panic!("a shape slot takes `El` of a code")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::ShapeCode(e.ind("T").tag)));
        // The arity is an *application* to the shape's own binder, because the
        // slot is read one binder deep — §2.1's asymmetry, pinned.
        let Some((fun, arg)) = crate::spelling::app_of(&aref) else {
            panic!("an arity slot takes an application, not a code")
        };
        assert!(e.el.is_gen_ref(fun, GenDef::ArityFn(e.ind("T").tag)));
        assert_eq!(**arg, Term::Var(LocalVar(0)));
        let respelled = Type::Wf {
            level: l.clone(),
            shape: Rc::new(sref),
            arity: Rc::new(aref),
        };
        assert!(e.el.conv_types(&e.cx, &respelled, &t_ty, &l));
        assert!(e.el.conv_types(&e.cx, &t_ty, &respelled, &l));
    }

    /// The **decode look-alike** (design §2.3), which is the copy a naive
    /// guard misses. Since `T#tycode` is spelled over its slot pair
    /// (`issues/elaborator-canonical-type-spelling.md`, 2026-09-23) the
    /// reference reduces to exactly the pair every constructor value carries,
    /// `Wf(El (T#shape^δ); app(T#arity^δ; x))`, which `Elaborator::whnf`
    /// unspells back to the inline lowering; and one δ further, the shape
    /// reference decodes to `El ⌜S⌝` — the look-alike the guard must still
    /// accept, or the whole constructor-value site declines silently.
    #[test]
    fn the_decoded_shape_spelling_respells_too() {
        let e = env();
        let (t_ty, l) = e.lowered("T");
        let Type::Wf { shape, arity, .. } = &t_ty else {
            panic!("T is recursive")
        };
        let whole =
            e.el.respell_ty(&e.cx, &t_ty)
                .expect("T's lowering respells");
        let stepped = heather_kernel::reduce::whnf_type_delta(
            &whole,
            &e.cx.gamma,
            heather_kernel::reduce::Defs::transparent(&e.el.psi),
            e.el.fuel,
        )
        .expect("the reference reduces");
        let (sref, aref) = e.el.wf_slot_refs(&e.cx, shape, arity).expect("T's slots are named");
        let Type::Wf { shape: s2, arity: a2, .. } = &stepped else {
            panic!("it reduces to a `Wf`")
        };
        assert_eq!(**s2, sref);
        assert_eq!(**a2, aref);
        assert_eq!(e.el.unspell_wf_slots(&stepped), Some(t_ty.clone()));
        // One δ of the shape reference: `El` of the shape's code, which is
        // the emission spelling of `S` (field types named, as a payload
        // code's are).
        let emitted = e.el.respell_ty_deep(&e.cx, shape, 0);
        let decoded_shape = Type::El {
            level: l.clone(),
            tm: Rc::new(crate::code::code_of(emitted.as_ref().unwrap_or(shape)).expect("a shape has a code")),
        };
        assert!(e.el.wf_slot_refs(&e.cx, &decoded_shape, arity).is_some());
    }

    /// The named pair with one slot swapped is not a spelling of `T`, and
    /// the unspell leaves it alone rather than handing back `T`'s lowering.
    #[test]
    fn a_swapped_slot_pair_does_not_unspell() {
        let e = env();
        let (t_ty, _) = e.lowered("T");
        let (u_ty, _) = e.lowered("U");
        let (Type::Wf { level, shape: ts, arity: ta }, Type::Wf { shape: us, arity: ua, .. }) = (&t_ty, &u_ty) else {
            panic!("T and U are recursive")
        };
        let (t_sref, _) = e.el.wf_slot_refs(&e.cx, ts, ta).expect("T's slots are named");
        let (_, u_aref) = e.el.wf_slot_refs(&e.cx, us, ua).expect("U's slots are named");
        let swapped = Type::Wf { level: level.clone(), shape: Rc::new(t_sref), arity: Rc::new(u_aref) };
        assert_eq!(e.el.unspell_wf_slots(&swapped), None);
    }

    /// The look-alike negative, in this round's discipline: the shape names
    /// `T` but the arity is **not** `T`'s. Without the pair comparison the
    /// slots would be spelled with `T`'s references and the `Wf` would mean a
    /// different type — a wrong annotation, not a rejection.
    #[test]
    fn a_wf_with_the_wrong_arity_declines() {
        let e = env();
        let (t_ty, _) = e.lowered("T");
        let Type::Wf { shape, arity, .. } = &t_ty else {
            panic!("T is recursive")
        };
        // Every label gets one more child than it should.
        let bumped = Term::Succ(Rc::clone(arity));
        assert!(e.el.wf_slot_refs(&e.cx, shape, &bumped).is_none());
        // …and the mirror: `U`'s shape with `T`'s arity is not `U`'s pair.
        let (u_ty, _) = e.lowered("U");
        let Type::Wf { shape: ushape, .. } = &u_ty else {
            panic!("U is recursive")
        };
        assert!(e.el.wf_slot_refs(&e.cx, ushape, arity).is_none());
    }

    /// A constructor **value** carries the references — the site the
    /// 2026-08-13 re-attribution named, pinned structurally rather than
    /// assumed, at a *literal* value (axis 1's first half).
    #[test]
    fn a_constructor_value_carries_the_slot_references() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source("fn mk() -> T { T1(1, T0) }")
            .expect("elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Supf { shape, arity, .. } = &**body else {
            panic!("a tier-1 value is a `sup_f`")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let Type::El { tm, .. } = &**shape else {
            panic!("the shape slot is the reference")
        };
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::ShapeCode(e.ind("T").tag)));
        let Some((fun, _)) = crate::spelling::app_of(arity) else {
            panic!("the arity slot is the application")
        };
        assert!(e.el.is_gen_ref(&fun.shift_global(grew), GenDef::ArityFn(e.ind("T").tag)));
    }

    /// …and a `match` carries them in its `elim_Wf`, over a **neutral**
    /// scrutinee (axis 1's second half).
    #[test]
    fn a_match_carries_the_slot_references_in_its_elim() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source(
            "fn depth2(t: T) -> Nat { match t { T0 => 0, T1(x, r) => 1, T2(y, r) => 2 } }",
        )
        .expect("elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Lam { body, .. } = &**body else {
            panic!("one parameter, one λ")
        };
        let Term::ElimWf { shape, arity, .. } = &**body else {
            panic!("tier 1 lowers to `elim_Wf`")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let Type::El { tm, .. } = &**shape else {
            panic!("the shape slot is the reference")
        };
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::ShapeCode(e.ind("T").tag)));
        let Some((fun, _)) = crate::spelling::app_of(arity) else {
            panic!("the arity slot is an application")
        };
        assert!(e.el.is_gen_ref(&fun.shift_global(grew), GenDef::ArityFn(e.ind("T").tag)));
    }

    /// The four axes with the slot spelling in place, including the one the
    /// slots are load-bearing for: a **container** field, whose branch arity is
    /// `Succ^m(len)` read out of the label — the one place the arity term is
    /// not a literal, so a mis-spelled arity slot shows up as a kernel
    /// rejection here and nowhere else.
    #[test]
    fn the_slot_spelling_checks_and_computes_across_the_axes() {
        let mut e = env();
        e.el.elab_source(
            "
inductive Rose { RNode(label: Nat, len: Nat, kids: [Rose; len]) }
fn rlabel(r: Rose) -> Nat { match r { RNode(label, len, kids) => label } }
fn rmk(n: Nat) -> Rose { RNode(n, 0, []) }
theorem rlabel_literal(): rlabel(RNode(4, 0, [])) = 4 { refl }
theorem rlabel_nonzero(): rlabel(RNode(4, 1, [RNode(1, 0, [])])) = 4 { refl }
theorem rlabel_neutral(n: Nat): rlabel(RNode(n, 0, [])) = n { refl }
theorem rmk_computes(): rlabel(rmk(9)) = 9 { refl }
",
        )
        .expect("a container declaration elaborates with slot references");
        let r =
            e.el.elab_source("theorem rlabel_wrong(): rlabel(RNode(4, 0, [])) = 5 { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }

    // -- a flat declaration's spine codes -----------------------------------
    // (`issues/inductive-spelling-codes-nonrecursive.md`)

    /// The registration boundary: a **non-recursive** declaration with at
    /// least two constructors names every payload and every suffix sum but
    /// the last (which *is* the last payload); a recursive one keeps its
    /// `D#shape`/`D#arity` pair and gets none of these (docs/wf-shape-code-
    /// design.md §5.1's rejection stands); a parameterized one is `TyCode`'s
    /// boundary, inherited.
    #[test]
    fn a_flat_declaration_names_its_payloads_and_suffixes_and_a_recursive_one_does_not() {
        let e = env();
        let flat = e.ind("Flat").tag;
        for k in 0..3 {
            assert!(
                e.el.gen_ref(&e.cx, GenDef::PayloadCode(flat, k)).is_some(),
                "`Flat` should have a `#payload{k}`"
            );
        }
        assert!(e.el.gen_ref(&e.cx, GenDef::SuffixCode(flat, 0)).is_some());
        // `tails[1]` is `⟦FC⟧` itself: no definition of its own.
        assert!(e.el.gen_ref(&e.cx, GenDef::SuffixCode(flat, 1)).is_none());
        assert!(e.el.types.gdefs().has_spine_code_entry(flat));
        for name in ["T", "U", "Box"] {
            let tag = e.ind(name).tag;
            assert!(e.el.gen_ref(&e.cx, GenDef::PayloadCode(tag, 0)).is_none(), "`{name}`");
            assert!(e.el.gen_ref(&e.cx, GenDef::SuffixCode(tag, 0)).is_none(), "`{name}`");
            assert!(!e.el.types.gdefs().has_spine_code_entry(tag));
        }
    }

    /// What the references *are*: the emission spine of `⟦Flat⟧` carries
    /// `El (Flat#payloadₖ^δ)` at every constructor, `El (Flat#suffix₀^δ)` at
    /// the first tail and the *last payload's* reference at the last tail —
    /// each convertible with the inline component it replaces, in both
    /// directions (conservativity at the spine's granularity). The scan-based
    /// `respell_ty` agrees with the positional answer, and the whole type
    /// still respells to `TyCode`, never to a component.
    #[test]
    fn the_spine_references_are_the_components_codes() {
        let e = env();
        let (flat_ty, l) = e.lowered("Flat");
        let flat = e.ind("Flat").tag;
        let spine = e.el.spine(&flat_ty, &l, 3, SPAN).expect("a spine");
        let emit = e.el.respell_spine(&e.cx, &spine);
        for (k, ((inline, lk), (r, _))) in spine.ctors.iter().zip(&emit.ctors).enumerate() {
            let Type::El { tm, level } = &**r else {
                panic!("payload {k} takes `El` of a code")
            };
            assert_eq!(level, lk);
            assert!(e.el.is_gen_ref(tm, GenDef::PayloadCode(flat, k)));
            assert!(e.el.conv_types(&e.cx, r, inline, lk));
            assert!(e.el.conv_types(&e.cx, inline, r, lk));
            assert_eq!(e.el.spine_type_ref(&e.cx, flat, inline).as_ref(), Some(&**r));
            // …but never from the deep walk: a component is named only by
            // position at emission (the tag-type look-alike, below).
            assert!(e.el.respell_ty(&e.cx, inline).is_none());
        }
        let Type::El { tm, .. } = &*emit.tails[0].0 else {
            panic!("the first tail takes `El` of a code")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::SuffixCode(flat, 0)));
        assert!(e.el.conv_types(&e.cx, &emit.tails[0].0, &spine.tails[0].0, &spine.tails[0].1));
        assert!(e.el.conv_types(&e.cx, &spine.tails[0].0, &emit.tails[0].0, &spine.tails[0].1));
        assert_eq!(
            e.el.spine_type_ref(&e.cx, flat, &spine.tails[0].0).as_ref(),
            Some(&*emit.tails[0].0)
        );
        let Type::El { tm, .. } = &*emit.tails[1].0 else {
            panic!("the last tail takes `El` of a code")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::PayloadCode(flat, 2)));
        // The whole is still the whole.
        let Type::El { tm, .. } = e.el.respell_ty(&e.cx, &flat_ty).expect("respells") else {
            panic!("`El` of a code")
        };
        assert!(e.el.is_gen_ref(&tm, GenDef::TyCode(flat)));
    }

    /// The whole-type code of a flat declaration is spelled over its spine's
    /// names: the kernel's δ + decode of `El (Flat#tycode^δ)` stops at a sum
    /// of two **neutral** references — which is what makes a label check
    /// against it one δ and an `==` — and the elaborator's own `whnf` of that
    /// reduct is the inline `⟦Flat⟧` again, so no structural reader sees the
    /// names (docs/wf-shape-code-design.md §3.3's line, one level down).
    #[test]
    fn a_flat_whole_type_code_decodes_through_its_spine_and_unspells_at_whnf() {
        let e = env();
        let (flat_ty, _) = e.lowered("Flat");
        let flat = e.ind("Flat").tag;
        let whole = e.el.respell_ty(&e.cx, &flat_ty).expect("respells");
        let stepped = heather_kernel::reduce::whnf_type_delta(
            &whole,
            &e.cx.gamma,
            heather_kernel::reduce::Defs::transparent(&e.el.psi),
            e.el.fuel,
        )
        .expect("the reference reduces");
        let Type::Sum { lhs, rhs, .. } = &stepped else {
            panic!("a flat declaration decodes to a sum")
        };
        let (Type::El { tm: l, .. }, Type::El { tm: r, .. }) = (&**lhs, &**rhs) else {
            panic!("both components are `El` of a code")
        };
        assert!(e.el.is_gen_ref(l, GenDef::PayloadCode(flat, 0)));
        assert!(e.el.is_gen_ref(r, GenDef::SuffixCode(flat, 0)));
        assert_eq!(e.el.whnf(&e.cx, &stepped, SPAN).expect("whnf"), flat_ty);
        assert_eq!(e.el.whnf(&e.cx, &whole, SPAN).expect("whnf"), flat_ty);
        assert_eq!(e.el.tag_of(&e.el.whnf(&e.cx, &stepped, SPAN).unwrap()).map(|i| i.tag), Some(flat));
    }

    /// The look-alike negatives, in `mod fingerprint`'s discipline. `Flat2`
    /// differs from `Flat` only in its tag: its spine takes **its own** names
    /// by position, and offering one declaration's component under the
    /// other's tag declines. A forged payload (the right tag, a wrong field)
    /// and a forged suffix (`⟦FB⟧ + Unit`) decline too — without the
    /// structural guard those would be spelled as `Flat`'s references and
    /// mean a different type.
    #[test]
    fn a_component_that_is_not_the_registered_one_declines() {
        let e = env();
        let (flat_ty, l) = e.lowered("Flat");
        let (flat2_ty, l2) = e.lowered("Flat2");
        let (flat, flat2) = (e.ind("Flat").tag, e.ind("Flat2").tag);
        let spine2 = e.el.spine(&flat2_ty, &l2, 3, SPAN).expect("a spine");
        let emit2 = e.el.respell_spine(&e.cx, &spine2);
        let Type::El { tm, .. } = &*emit2.ctors[1].0 else {
            panic!("`Flat2`'s payload respells")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::PayloadCode(flat2, 1)));
        assert!(e.el.spine_type_ref(&e.cx, flat, &spine2.ctors[1].0).is_none());
        assert!(e.el.spine_type_ref(&e.cx, flat, &spine2.tails[0].0).is_none());
        let spine = e.el.spine(&flat_ty, &l, 3, SPAN).expect("a spine");
        // `⟦FB⟧` with its `Nat` field replaced: `Σ(tag). Σ(Unit). Unit`.
        let Type::Sigma { fst_level, snd_level, fst, snd } = &*spine.ctors[1].0 else {
            panic!("a payload is a Σ")
        };
        let Type::Sigma { snd: rest, .. } = &**snd else {
            panic!("`FB` has a field")
        };
        let forged = Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: Rc::clone(fst),
            snd: Rc::new(Type::Sigma {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst: Rc::new(Type::Unit { level: Level::Zero }),
                snd: Rc::clone(rest),
            }),
        };
        assert_eq!(e.el.tag_of(&forged).map(|i| i.tag), Some(flat));
        assert!(e.el.respell_ty(&e.cx, &forged).is_none());
        assert!(e.el.spine_type_ref(&e.cx, flat, &forged).is_none());
        let forged_suffix = Type::Sum {
            lhs_level: spine.ctors[1].1.clone(),
            rhs_level: Level::Zero,
            lhs: Rc::clone(&spine.ctors[1].0),
            rhs: Rc::new(Type::Unit { level: Level::Zero }),
        };
        assert_eq!(e.el.tag_of(&forged_suffix).map(|i| i.tag), Some(flat));
        assert!(e.el.respell_ty(&e.cx, &forged_suffix).is_none());
        assert!(e.el.spine_type_ref(&e.cx, flat, &forged_suffix).is_none());
    }

    /// The tag-type look-alike that made the scan unsafe as a fallback of
    /// `respell_ty`: the declaration with nominal tag 0 has a nullary payload
    /// `Σ(Unit). Unit`, which is the digit-1 component of every later tag
    /// type. A monomorphized instance whose tag type carries that digit must
    /// respell nothing inside its tags, and its constructor values must still
    /// build at the respelled statement type.
    #[test]
    fn a_tag_types_digit_is_never_spelled_as_a_payload() {
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.elab_source(
            "
inductive Bool { True, False }
inductive Option<A> { None, Some(A) }
fn or_else(d: Nat, o: Option<Nat>) -> Nat { match o { None => d, Some(x) => x } }
theorem s1(): or_else(3, Some(5)) = 5 { refl }
theorem s2(): or_else(3, None) = 3 { refl }
",
        )
        .expect("a monomorphized instance elaborates beside a coded tag-0 declaration");
    }

    /// A constructor **value** of a flat declaration carries the type it was
    /// checked at — `El (Flat#tycode^δ)`, the reference, not its unfolding —
    /// on its outermost injection, and **nothing** on the injections inside
    /// it (`docs/intro-by-type-design.md` §4.1). Until stage 2 every level
    /// of the path carried spine references in its `Inl`/`Inr` components;
    /// the checked spelling writes no components at all. Pinned structurally
    /// at a literal value, in the checking position a `fn`'s declared return
    /// type provides.
    #[test]
    fn a_flat_constructor_value_carries_the_spine_references() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source("fn mk() -> Flat { FB(1) }").expect("elaborates");
        let GlobalBinding::Tm { body: Some(body), .. } =
            e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let flat = e.ind("Flat").tag;
        let is_ref = |ty: &Type, key: GenDef| {
            let Type::El { tm, .. } = ty else { return false };
            e.el.is_gen_ref(&tm.shift_global(grew), key)
        };
        let Term::InrAt { ty: Some(ty), val } = &**body else {
            panic!("`FB` is the second constructor: an annotated `inr@`, got {body:?}")
        };
        assert!(is_ref(ty, GenDef::TyCode(flat)), "the declared type, as a reference: {ty:?}");
        let Term::InlAt { ty: None, .. } = &**val else {
            panic!("…of an unannotated `inl@`, got {val:?}")
        };
    }

    /// …and a `match` on a flat declaration carries them in every `Case` of
    /// its tag tree, over a **neutral** scrutinee.
    #[test]
    fn a_flat_match_carries_the_spine_references_in_its_cases() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source(
            "fn sel(x: Flat) -> Nat { match x { FA => 0, FB(n) => n, FC(m, k) => m } }",
        )
        .expect("elaborates");
        let GlobalBinding::Tm { body: Some(body), .. } =
            e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let flat = e.ind("Flat").tag;
        let is_ref = |ty: &Type, key: GenDef| {
            let Type::El { tm, .. } = ty else { return false };
            e.el.is_gen_ref(&tm.shift_global(grew), key)
        };
        let mut cur: &Term = body;
        while let Term::Lam { body, .. } = cur {
            cur = body;
        }
        let Term::Case { lhs, rhs, case_r, .. } = cur else {
            panic!("tier 0 lowers to a `case` tree")
        };
        assert!(is_ref(lhs, GenDef::PayloadCode(flat, 0)));
        assert!(is_ref(rhs, GenDef::SuffixCode(flat, 0)));
        let Term::Case { lhs, rhs, .. } = &**case_r else {
            panic!("the inner `case`")
        };
        assert!(is_ref(lhs, GenDef::PayloadCode(flat, 1)));
        assert!(is_ref(rhs, GenDef::PayloadCode(flat, 2)));
    }

    /// A **monomorphized** recursive `Wf` — `Box<Flat>`, which no code names —
    /// respells its shape's components *and* its arity's `Case` annotations
    /// alike, or not at all (the parameterized slice of
    /// `issues/inductive-spelling-codes-nonrecursive.md`): a respelled shape
    /// over an inline arity is the mismatch the kernel paid at every `Wf`
    /// occurrence of a `List<Instruction>` value. Pinned structurally, and
    /// convertible with the inline lowering both ways.
    #[test]
    fn a_monomorphized_wf_respells_its_shape_and_arity_alike() {
        let e = env();
        let (flat_ty, fl) = e.lowered("Flat");
        let (box_ty, l) =
            e.el.lower_instance(&e.cx, &e.ind("Box"), &[(flat_ty.clone(), fl)], &[], SPAN)
                .expect("`Box<Flat>` lowers");
        // Since `docs/per-instantiation-type-codes-design.md` the *whole*
        // instantiation has a name, so the chokepoint hands back the code
        // function's application — and the slot pair, which may not hold a
        // reference to the whole (§8), asks its own question.
        let whole = e.el.respell_ty_deep(&e.cx, &box_ty, 0).expect("the instance respells");
        assert!(matches!(&whole, Type::El { .. }), "{whole:?}");
        assert_eq!(e.el.unspell_here(&whole).as_ref(), Some(&box_ty));
        let Type::Wf { shape: s0, arity: a0, .. } = &box_ty else {
            panic!("a recursive lowering is a `Wf`")
        };
        let (shape, arity) =
            e.el.emit_wf_slots(&e.cx, s0, a0, 0).expect("its components respell");
        let r = Type::Wf {
            level: l.clone(),
            shape: Rc::clone(&shape),
            arity: Rc::clone(&arity),
        };
        // The shape's `BCons` payload carries the field as `El (Flat#tycode^δ)`…
        let Type::Sum { rhs, .. } = &*shape else {
            panic!("two constructors: a sum")
        };
        let Type::Sigma { snd, .. } = &**rhs else {
            panic!("a payload is a Σ")
        };
        let Type::Sigma { fst, .. } = &**snd else {
            panic!("`BCons` has a field")
        };
        let Type::El { tm, .. } = &**fst else {
            panic!("the field respells to `El` of a code")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("Flat").tag)));
        // …and so does the arity's `Case` annotation for the same summand,
        // one binder deeper (the shape's own).
        let Term::Case { rhs: case_rhs, .. } = &*arity else {
            panic!("the arity is a case tree")
        };
        let Type::Sigma { snd, .. } = &**case_rhs else {
            panic!("the `Case`'s right summand is the payload")
        };
        let Type::Sigma { fst, .. } = &**snd else {
            panic!("`BCons` has a field")
        };
        let Type::El { tm, .. } = &**fst else {
            panic!("the arity's annotation respells with the shape")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("Flat").tag)));
        assert!(e.el.conv_types(&e.cx, &r, &box_ty, &l));
        assert!(e.el.conv_types(&e.cx, &box_ty, &r, &l));
        // …and the spelling checks and computes end to end.
        let mut e = e;
        e.el.elab_source(
            "
fn bhead(b: Box<Flat>) -> Flat { match b { BNil => FA, BCons(a, r) => a } }
fn bmk(n: Nat) -> Box<Flat> { BCons(FB(n), BCons(FA, BNil)) }
theorem bhead_literal(): bhead(BCons(FC(1, 2), BNil)) = FC(1, 2) { refl }
theorem bhead_neutral(n: Nat): bhead(bmk(n)) = FB(n) { refl }
",
        )
        .expect("a monomorphized `Wf` elaborates with the consistent spelling");
        let r = e.el.elab_source("theorem bhead_wrong(): bhead(bmk(1)) = FA { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }

    /// The four axes with the spine spelling in place: a literal and a
    /// neutral scrutinee, a checking position (a value built at the declared
    /// return type, and one built at a *match arm's* expected type), an open
    /// element type (a parameterized flat declaration, which names nothing
    /// and elaborates beside the coded ones), a computation pinned by `refl`,
    /// and a false-equation negative control.
    #[test]
    fn the_spine_spelling_checks_and_computes_across_the_axes() {
        let mut e = env();
        e.el.elab_source(
            "
fn sel(x: Flat) -> Nat { match x { FA => 0, FB(n) => n, FC(m, k) => m } }
fn swap(x: Flat) -> Flat { match x { FA => FA, FB(n) => FB(n), FC(m, k) => FC(k, m) } }
inductive Opt<A> { ONone, OSome(a: A) }
fn omap<A>(x: Opt<A>) -> Opt<A> { match x { ONone => ONone, OSome(a) => OSome(a) } }
fn oflat(x: Opt<Flat>) -> Flat { match x { ONone => FA, OSome(f) => swap(f) } }
theorem sel_literal(): sel(FB(3)) = 3 { refl }
theorem sel_neutral(n: Nat): sel(FB(n)) = n { refl }
theorem swap_literal(): swap(FC(1, 2)) = FC(2, 1) { refl }
theorem swap_neutral(m: Nat, k: Nat): sel(swap(FC(m, k))) = k { refl }
theorem oflat_computes(): sel(oflat(OSome(FC(4, 5)))) = 5 { refl }
",
        )
        .expect("a flat declaration elaborates with spine references");
        let r = e.el.elab_source("theorem sel_wrong(): sel(FB(3)) = 4 { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }

    // -- emission-site audit (issues/emission-site-respell-audit.md) -------

    /// An application of a **local** callee spells its `dom`/`cod`
    /// annotations with the same references a global's statement carries:
    /// the two spellings met at every use of a lemma whose statement embeds
    /// `operation(…)` over a binder (`Sigma`/`Sigma`, `Pi`/`Pi` on the x86
    /// rail). Pinned structurally on a closed and an *open* domain (`[T; n]`
    /// under `n`, so the reference's tail has to be right at depth), then
    /// checked and computed at a literal and a neutral argument, with the
    /// "both sides alike" case itself — a section substituted into a
    /// statement's embedded application — and a false-equation control.
    #[test]
    fn a_local_callees_application_respells_its_annotations() {
        let mut e = env();
        e.el.elab_source("fn app_local(f: T -> Flat, t: T) -> Flat { f(t) }")
            .expect("elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let mut cur: &Term = body;
        while let Term::Lam { body, .. } = cur {
            cur = body;
        }
        // Since `docs/app-by-head-type-design.md` the call is `app@(f; t)`:
        // it states no `dom`/`cod`, so there is no annotation left for the
        // binder's inline type to leak into — the respell's whole subject is
        // gone. What stays pinned is that the call is written that way at a
        // local head, and (below) that everything still checks and computes.
        let Term::AppAt { fun, .. } = cur else {
            panic!("the body is the call, written `app@`")
        };
        assert!(matches!(&**fun, Term::Var(_)), "a local callee");

        // An open domain: the element type respells inside the `Vec`, at a
        // depth of three binders, and the kernel agrees with the binder's own
        // (cascade-respelled) type — a wrong tail here is a rejection.
        e.el.elab_source("fn app_open(n: Nat, f: [T; n] -> Nat, v: [T; n]) -> Nat { f(v) }")
            .expect("an open domain respells at depth");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let mut cur: &Term = body;
        while let Term::Lam { body, .. } = cur {
            cur = body;
        }
        assert!(matches!(cur, Term::AppAt { .. }), "the body is the call, written `app@`");

        // The statement side of the same pair: a lemma whose hypothesis
        // embeds `op(a)` carries the reference in that application's `dom`…
        e.el.elab_source(
            "theorem eq_op(op: Flat -> Flat, a: Flat, h: op(a) = FA): op(a) = FA { h }",
        )
        .expect("elaborates");
        let GlobalBinding::Tm { ty, .. } = e.el.psi.bindings.last().expect("a binding") else {
            panic!("a theorem is a term binding")
        };
        let mut cur: &Type = ty;
        for _ in 0..2 {
            let Type::Pi { cod, .. } = cur else { panic!("three Πs") };
            cur = cod;
        }
        let Type::Pi { dom, .. } = cur else { panic!("the hypothesis binder") };
        let Type::Id { lhs, .. } = &**dom else { panic!("`h` is an equation") };
        assert!(
            matches!(&**lhs, Term::AppAt { .. }),
            "an application embedded in a statement is `app@`, with no `dom` to spell"
        );
        // …so a section substituted for `op` — whose binder type is copied off
        // the respelled Π — meets its own spelling at the use, and everything
        // still checks and computes.
        e.el.elab_source(
            "
theorem use_eq(): FA = FA { eq_op(λ (x: Flat) => FA, FB(1), refl) }
theorem app_local_literal(): app_local(λ (x: T) => FA, T0) = FA { refl }
theorem app_local_neutral(t: T): app_local(λ (x: T) => FB(1), t) = FB(1) { refl }
theorem app_open_neutral(n: Nat, v: [T; n]): app_open(n, λ (w: [T; n]) => n, v) = n { refl }
",
        )
        .expect("local applications check and compute with the respelled annotations");
        let r = e.el.elab_source("theorem app_wrong(): app_local(λ (x: T) => FA, T0) = FB(0) { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }

    /// A constructor value of a **monomorphized** recursive declaration —
    /// `Box<Flat>`, which has no slots to name — spells its `sup_f`'s shape
    /// and arity with the same component respell its label's injection
    /// annotations take, so the label checks against the shape syntactically
    /// (`Sum` vs `Sum` on the x86 rail: the inline shape against a respelled
    /// `Inr`). Pinned as *equality* of the two spellings, on a closed and an
    /// open instance, then checked and computed with a negative control.
    #[test]
    fn a_monomorphized_constructor_value_spells_its_shape_and_label_alike() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source("fn bmk1(n: Nat) -> Box<Flat> { BCons(FB(n), BNil) }")
            .expect("elaborates");
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Lam { body, .. } = &**body else { panic!("one λ") };
        let Term::Supf { shape, label, children, .. } = &**body else {
            panic!("a recursive constructor value is a `sup_f`")
        };
        let Type::Sum { lhs, rhs, .. } = &**shape else {
            panic!("two constructors: the shape is a sum")
        };
        // The shape's `BCons` payload carries the field as the reference…
        let Type::Sigma { snd, .. } = &**rhs else { panic!("a payload is a Σ") };
        let Type::Sigma { fst, .. } = &**snd else { panic!("`BCons` has a field") };
        let Type::El { tm, .. } = &**fst else {
            panic!("the `sup_f`'s shape respells with the label, not inline")
        };
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::TyCode(e.ind("Flat").tag)));
        // …and the label's one annotation is *that* shape
        // (`docs/intro-by-type-design.md` §4.1): the checked spelling carries
        // the sum whole, where the component spelling carried its summands.
        let _ = lhs;
        let Term::InrAt { ty: Some(at), .. } = &**label else {
            panic!("`BCons` is the second constructor: one annotated `inr@`, got {label:?}")
        };
        assert_eq!(**at, **shape, "the injection's annotation is the `sup_f`'s shape");
        // The child `BNil` is built at the inline expected type and spells
        // its own `sup_f` the same way.
        let mut child: &Term = children;
        while let Term::Lam { body, .. } = child {
            child = body;
        }
        let mut found = false;
        let mut stack = vec![child];
        while let Some(t) = stack.pop() {
            match t {
                Term::Supf { shape: s, label: l, .. } => {
                    let Term::InlAt { ty: Some(at), .. } = &**l else {
                        panic!("`BNil` is the first constructor: one annotated `inl@`")
                    };
                    assert_eq!(**at, **s);
                    found = true;
                }
                Term::Case { case_l, case_r, .. } => {
                    stack.push(case_l);
                    stack.push(case_r);
                }
                Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                    stack.push(fst);
                    stack.push(snd);
                }
                Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                    stack.push(fun);
                    stack.push(arg);
                }
                _ => {}
            }
        }
        assert!(found, "the child `BNil` is in the children function");

        e.el.elab_source(
            "
fn bhead1(b: Box<Flat>) -> Flat { match b { BNil => FA, BCons(a, r) => a } }
fn bmk_open(n: Nat, v: [T; n]) -> Box<[T; n]> { BCons(v, BNil) }
fn bhead_open(n: Nat, b: Box<[T; n]>, d: [T; n]) -> [T; n] {
    match b { BNil => d, BCons(a, r) => a }
}
theorem bmk1_literal(): bhead1(bmk1(3)) = FB(3) { refl }
theorem bmk1_neutral(n: Nat): bhead1(bmk1(n)) = FB(n) { refl }
theorem bmk_open_neutral(n: Nat, v: [T; n], d: [T; n]): bhead_open(n, bmk_open(n, v), d) = v { refl }
",
        )
        .expect("monomorphized values check and compute with shape and label alike");
        let r = e.el.elab_source("theorem bmk1_wrong(): bhead1(bmk1(3)) = FA { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }

    /// A projection off a record type that arrives as a **code literal** —
    /// the quote of a `→ Type` body — spells every link of its `fst`/`snd`
    /// chain inline (`decode_deep`), so the pair type one link writes is
    /// exactly the type the next link's pair infers (`Sigma` vs `El⌜⌝` on
    /// the x86 rail, one whole-literal evaluation per link). Pinned as the
    /// equality of adjacent links, then checked and computed at a literal
    /// and a neutral field, with a negative control.
    #[test]
    fn a_projection_off_a_code_literal_spells_adjacent_links_alike() {
        let mut e = env();
        e.el.elab_source(
            "
record Pr { a: Flat, b: T }
fn PrT() -> Type { Pr }
fn getb(p: PrT()) -> T { p.b }
",
        )
        .expect("a projection off `El ⌜⟦Pr⟧⌝` elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Lam { body, .. } = &**body else { panic!("one λ") };
        // `p.b` is entry 2 of the spine: `fst@(snd@(snd@(p)))`. The checked
        // projections carry no annotation at all (`docs/intro-by-type-design.md`
        // §2.1), so the adjacent-link agreement this test pinned for the
        // component spelling has nothing left to compare: the receiver infers
        // each link's type. What stays pinned is the chain's shape, and below,
        // that it computes on a literal and on a neutral.
        let Term::FstAt { pair: p2 } = &**body else {
            panic!("a projection is a `fst@`, got {body:?}")
        };
        let Term::SndAt { pair: p1 } = &**p2 else { panic!("…of a `snd@`") };
        let Term::SndAt { pair: p0 } = &**p1 else { panic!("…of a `snd@`") };
        assert!(matches!(&**p0, Term::Var(_)));

        e.el.elab_source(
            "
fn mkpr(x: T) -> PrT() { Pr(a := FA, b := x) }
theorem getb_literal(): getb(mkpr(T0)) = T0 { refl }
theorem getb_neutral(x: T): getb(mkpr(x)) = x { refl }
",
        )
        .expect("the projection checks and computes");
        let r = e.el.elab_source("theorem getb_wrong(): getb(mkpr(T0)) = T1(0, T0) { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }

    // -- the emission walker (design §2.5) ----------------------------------

    /// The fast-lane twin of the whole-library audit
    /// (`crates/elab/tests/ir_v1.rs::the_full_ir_library_checks`): a corpus
    /// small enough to run every round, over the three sites
    /// `issues/emission-spelling-chokepoint.md` names — a theorem whose
    /// `refl` fills a `Refl.ty`, a constructor literal of a coded declaration
    /// in a checking position, and a **written** lambda binder — on
    /// `docs/testing-generated-terms.md`'s axes: a literal and a neutral
    /// scrutinee, an open element type (`Box<[T; n]>`, whose monomorphized
    /// `Wf` has no whole-type reference), and a checking position.
    ///
    /// The positive half is "no slot listed". The negative controls are
    /// hand-built terms carrying the registry's **inline** copy where a
    /// reference exists: without them "no findings" is equally consistent
    /// with a walker that visits nothing.
    #[test]
    fn the_emission_walk_lists_nothing_on_a_small_corpus_and_lists_a_planted_slot() {
        let mut e = env();
        e.el.enable_emission_walk();
        e.el.elab_source(
            "
fn tid3(t: T) -> T { t }
fn tlam() -> T -> T { λ (t: T) => t }
fn bmk3(n: Nat, v: [T; n]) -> Box<[T; n]> { BCons(v, BNil) }
fn fnext3(f: Flat) -> Flat { match f { FA => FB(1), FB(n) => FC(n, n), FC(m, k) => FA } }
record R3 { f: Flat }
fn mkr3() -> R3 { R3(f := FB(1)) }
theorem tid3_neutral(t: T): tid3(t) = t { refl }
theorem tlam_neutral(t: T): tlam()(t) = t { refl }
theorem fnext3_computes(): fnext3(FB(2)) = FC(2, 2) { refl }
",
        )
        .expect("the corpus elaborates");
        let findings = e.el.take_emission_findings();
        let listed: Vec<String> = findings
            .iter()
            .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
            .collect();
        assert!(
            findings.is_empty(),
            "every emitted slot already carries the chokepoint's spelling:\n{}",
            listed.join("\n")
        );

        // Control 1: a `Refl` whose element type is the inline lowering, the
        // spelling `read_expected_type`'s whnf hands back.
        let (t_ty, l) = e.lowered("T");
        let planted = Term::Refl {
            level: l.clone(),
            ty: Rc::new(t_ty.clone()),
            tm: Rc::new(Term::Var(LocalVar(0))),
        };
        let found = crate::emission_walk::walk_decl(&e.el, "planted", &Type::Nat, Some(&planted));
        assert_eq!(found.len(), 1, "exactly the planted slot");
        assert_eq!(found[0].slot, "Refl.ty");
        assert_eq!(found[0].depth, 0);

        // Control 2: the statement half, and a slot **under a binder** — the
        // depth is what a wrong shift would get wrong, and a closed type
        // hides one (axis 2).
        let stmt = Type::Pi {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(t_ty.clone()),
            cod: Rc::new(Type::Nat),
        };
        let under = Term::Lam {
            dom_level: l.clone(),
            cod_level: l.clone(),
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Refl {
                level: l,
                ty: Rc::new(t_ty),
                tm: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        let found = crate::emission_walk::walk_decl(&e.el, "planted", &stmt, Some(&under));
        let slots: Vec<(&str, u32)> = found.iter().map(|f| (f.slot, f.depth)).collect();
        assert_eq!(slots, vec![("stmt", 0), ("Refl.ty", 1)]);
        // …and what it would write there is `T`'s own reference, minted at
        // the binder's depth rather than the statement's — a closed type
        // hides the shift, so the depth is asserted rather than assumed.
        let (lowered, _) = e.lowered("T");
        let at0 = e.el.emit_ty(&e.cx, &lowered, 0).expect("`T`'s lowering respells");
        let Type::El { tm, .. } = &at0 else {
            panic!("the reference is an `El` of the code")
        };
        assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("T").tag)));
        let at1 = e.el.emit_ty(&e.cx, &lowered, 1).expect("…at the binder's depth too");
        assert_ne!(at0, at1, "the substitution tail is one longer under a binder");
        assert_eq!(found[1].emitted, format!("{at1:?}"));
    }

    /// The two residual sampler rows of `issues/conv-miss-residual-rows.md`
    /// (`El^δ` against `Sum`/`Sigma` at a constructor literal) pinned as the
    /// **designed** shape rather than a defect: a field's stated type is the
    /// declaration's whole-type reference, while the literal filling it
    /// synthesizes its type from its own injection annotations, which are the
    /// spine components. There is no slot in which the inferred side could
    /// carry the reference, so the rows are one δ and a compare each — and
    /// what this pins is that both sides are already exactly what `emit_ty`
    /// writes, so neither is a spelling *disagreement*.
    #[test]
    fn a_constructor_literal_and_the_field_type_it_fills_are_each_the_chokepoints_spelling() {
        let mut e = env();
        e.el.elab_source("record R4 { f: Flat }\nfn mkr4() -> R4 { R4(f := FB(1)) }")
            .expect("a record literal at a coded field type elaborates");
        let GlobalBinding::Tm {
            body: Some(body), ..
        } = e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        // `pair@^{R4}(tag_refl; pair@(FB(1); ⟨⟩))` since stage 2
        // (`docs/intro-by-type-design.md` §4.1): a record has no injection, so
        // its tuple's root carries the type it was checked at, and the field
        // links carry nothing. The field value carries the field's stated
        // type — the declaration's reference — on its outermost injection,
        // which is the one annotation that can meet an inferring position.
        let Term::PairAt { ty: Some(root), snd, .. } = &**body else {
            panic!("a record value is an annotated tuple, got {body:?}")
        };
        let Term::PairAt { ty: None, fst, .. } = &**snd else {
            panic!("…with an unannotated field link")
        };
        let Term::InrAt { ty: Some(field_ty), .. } = &**fst else {
            panic!("`FB` is the second constructor: an annotated `inr@`, got {fst:?}")
        };
        assert_ne!(
            **field_ty,
            e.lowered("Flat").0,
            "the field value's annotation is a reference, not the inline lowering"
        );
        for ann in [root, field_ty] {
            assert!(
                e.el.emit_ty(&e.cx, ann, 0).is_none(),
                "an annotation the chokepoint would still respell: {ann:?}"
            );
        }
    }

    /// A record with no named projections — a non-dependent spine,
    /// `register_rec_projs`'s boundary — is projected by `project_field`'s
    /// inline walk, whose annotations are read off the `whnf` of the record's
    /// own `El (D#tycode^δ)` reference: the registry's **inline** lowering,
    /// until 2026-09-10, while the tuple such a projection meets
    /// (`build_fields_skel`) spells every component through the chokepoint.
    /// Where a record *definition* projects one of its value parameters in a
    /// field type, every instance of that record then carried the inline
    /// spelling against the literal's — the `Sigma`/`Sigma` bucket of the x86
    /// fetch certificates (issues/unnameable-annotation-occurrences.md).
    /// Pinned three ways: the walker lists nothing on a projection body; the
    /// field type's `Fst` annotation *equals* the literal's `Pair` annotation
    /// at an instance; and the instance checks, computes, and refuses.
    #[test]
    fn a_projection_off_an_unnamed_spine_takes_the_chokepoints_spelling() {
        let mut e = env();
        e.el.enable_emission_walk();
        #[cfg(feature = "value-metrics")]
        e.el.enable_value_metrics();
        e.el.elab_source(
            "
record S5 { a: Flat, b: Nat }
fn s5a(s: S5) -> Flat { s.a }
record H5(s: S5) { ok: s.a = FA }
theorem h5_use(h: H5(S5(FA, 1))): H5(S5(FA, 1)) { h }
theorem s5a_literal(): s5a(S5(FB(2), 0)) = FB(2) { refl }
theorem s5a_neutral(s: S5): s5a(s) = s.a { refl }
",
        )
        .expect("a projection off an unnamed spine elaborates, checks and computes");
        let findings = e.el.take_emission_findings();
        let listed: Vec<String> = findings
            .iter()
            .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
            .collect();
        assert!(
            findings.is_empty(),
            "the walk's `Fst`/`Snd` annotations are already the chokepoint's:\n{}",
            listed.join("\n")
        );
        // `h5_use`'s binder is the inline instance `Σ(tag). Σ(ok : s.a = FA). Unit`
        // at `s := S5(FA, 1)`: the equation's left side is the walk's
        // `fst(snd(⟨tag, ⟨FA, ⟨1, ⟨⟩⟩⟩⟩))`, and its `Fst` annotation must be
        // the very type the literal's own field link states.
        let abs = e.el.lookup_global("h5_use").expect("`h5_use` is registered").abs as usize;
        let GlobalBinding::Tm { ty, .. } = e.el.psi.bindings.get(abs).expect("…and bound") else {
            panic!("a theorem is a term binding")
        };
        let Type::Pi { dom, .. } = &**ty else { panic!("`h5_use` binds `h`") };
        let Type::Sigma { snd, .. } = &**dom else { panic!("the instance is a Σ (tag first)") };
        let Type::Sigma { fst, .. } = &**snd else { panic!("…then the field") };
        let Type::Id { lhs, .. } = &**fst else { panic!("`ok` is an equation") };
        // Since stage 2 (`docs/intro-by-type-design.md` §2.1) the projection
        // carries no annotation and the literal only its root's, so the two
        // spellings this test held equal no longer exist to disagree: the
        // projection's type is read off the literal's.
        let Term::FstAt { pair } = &**lhs else { panic!("its left side projects `a`: {lhs:?}") };
        let Term::SndAt { pair } = &**pair else { panic!("…past the tag") };
        let Term::PairAt { ty: Some(root), snd, .. } = &**pair else {
            panic!("…off the annotated literal")
        };
        let Term::PairAt { ty: None, .. } = &**snd else { panic!("the literal's `a` link") };
        assert!(
            e.el.emit_ty(&e.cx, root, 0).is_none(),
            "the literal's annotation is the chokepoint's spelling: {root:?}"
        );
        // …and no `Sigma`/`Sigma` row appears in the module's miss table.
        #[cfg(feature = "value-metrics")]
        {
            let report = e.el.value_conv_miss_report().unwrap_or_default();
            assert!(
                !report.contains("expected=Sigma inferred=Sigma"),
                "a projection annotation still meets a differently spelled literal:\n{report}"
            );
        }
        // Negative control: an instance at a different literal is a different
        // type, spelling or no spelling.
        let r = e.el.elab_source("theorem h5_wrong(h: H5(S5(FA, 1))): H5(S5(FB(1), 1)) { h }");
        assert!(r.is_err(), "a mismatched instance must still be refused");
    }

    // -- the code *function* (docs/per-instantiation-type-codes-design.md) ---

    mod tycode_fn {
        //! `D#tycode_fn` — the per-instantiation spelling
        //! (`docs/per-instantiation-type-codes-design.md`).
        //!
        //! The same two obligations as the module above and the same
        //! discipline: emission is checked by elaborating real source, and
        //! recognition structurally, with a look-alike and a wrong-argument
        //! negative on every path.

        use super::*;

        fn code_fn_of(e: &Env, name: &str) -> Option<Term> {
            e.el.gen_ref(&e.cx, GenDef::TyCodeFn(e.ind(name).tag))
        }

        /// The instantiation `D<args>` as `lower_instance` writes it.
        fn instance(e: &Env, name: &str, args: &[(Type, Level)]) -> (Type, Level) {
            e.el.lower_instance(&e.cx, &e.ind(name), args, &[], SPAN)
                .expect("the instantiation lowers")
        }

        // -- registration boundary ------------------------------------------

        #[test]
        fn a_parameterized_declaration_gets_a_code_function_and_a_closed_one_does_not() {
            let e = env();
            for name in ["Box", "Two", "Box2"] {
                assert!(
                    code_fn_of(&e, name).is_some(),
                    "`{name}` is parameterized and should have a `#tycode_fn`"
                );
            }
            // The complement of `register_ty_code`'s boundary, exactly: a
            // closed declaration has the whole-type code and no function.
            for name in ["T", "U", "Flat"] {
                assert!(code_fn_of(&e, name).is_none(), "`{name}` is closed");
                assert!(e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind(name).tag)).is_some());
            }
            assert!(e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind("Box").tag)).is_none());
        }

        #[test]
        fn a_value_indexed_declaration_gets_a_code_function() {
            let e = env();
            // §2's asymmetry: a value parameter is abstracted by an ordinary
            // `Π` over its type, and a mixed telescope registers as one.
            for name in ["BV", "Mixed"] {
                assert!(code_fn_of(&e, name).is_some(), "`{name}` has value parameters");
            }
        }

        // -- the reference at an instantiation -------------------------------

        #[test]
        fn an_instantiation_is_spelled_as_the_code_functions_application() {
            let e = env();
            let (flat, fl) = e.lowered("Flat");
            let (inline, il) = instance(&e, "Box", &[(flat, fl)]);
            let r = e.el.respell_ty(&e.cx, &inline).expect("`Box<Flat>` respells");
            let Type::El { level, tm } = &r else {
                panic!("the spelling is `El` of an application")
            };
            assert_eq!(*level, il);
            let (key, args) = e.el.gen_app_of(tm).expect("an application of a definition");
            assert_eq!(key, GenDef::TyCodeFn(e.ind("Box").tag));
            assert_eq!(args.len(), 1);
            // Convertible both ways — the reference is a spelling change.
            assert!(e.el.conv_types(&e.cx, &r, &inline, &il));
            assert!(e.el.conv_types(&e.cx, &inline, &r, &il));
            // Idempotent: `tag_of` leaves an `El` of a neutral alone.
            assert!(e.el.respell_ty(&e.cx, &r).is_none());
            // …and the inverse restores the registry's own copy, not the
            // kernel's decode (§4.2): this is what every structural reader
            // and every use-site guard sees.
            assert_eq!(
                e.el.unspell_here(&r).expect("the applied reference unspells"),
                inline
            );
            assert_eq!(e.el.whnf(&e.cx, &r, SPAN).expect("whnf"), inline);
            assert_eq!(e.el.tag_of(&r).map(|i| i.tag), None);
        }

        #[test]
        fn a_wrong_argument_application_is_not_the_instance() {
            let e = env();
            let (flat, fl) = e.lowered("Flat");
            let (flat2, fl2) = e.lowered("Flat2");
            let (inline, il) = instance(&e, "Box", &[(flat, fl)]);
            let (other, _) = instance(&e, "Box", &[(flat2, fl2)]);
            let wrong = e.el.respell_ty(&e.cx, &other).expect("`Box<Flat2>` respells");
            assert!(
                !e.el.conv_types(&e.cx, &wrong, &inline, &il),
                "a wrong-argument application is a different type"
            );
            // …and the look-alike declaration's own instantiation is not this
            // one either, tags being nominal.
            let (look, ll) = instance(&e, "Box2", &[(e.lowered("Flat").0, e.lowered("Flat").1)]);
            let look_r = e.el.respell_ty(&e.cx, &look).expect("`Box2<Flat>` respells");
            let Type::El { tm, .. } = &look_r else { panic!("a reference") };
            assert_eq!(
                e.el.gen_app_of(tm).map(|(k, _)| k),
                Some(GenDef::TyCodeFn(e.ind("Box2").tag))
            );
            assert!(!e.el.conv_types(&e.cx, &look_r, &inline, &ll));
        }

        #[test]
        fn a_lookalike_declaration_does_not_match_the_template() {
            let e = env();
            // `Box` and `Box2` differ only in their nominal tags, and the
            // template is compared for equality at the position it puts its
            // own tag Σ (`issues/tag-types-collide-with-lowerings.md`).
            let (flat, fl) = e.lowered("Flat");
            let (b1, _) = instance(&e, "Box", &[(flat.clone(), fl.clone())]);
            assert_eq!(e.el.tag_of(&b1).map(|i| i.tag), Some(e.ind("Box").tag));
            // A closed declaration's lowering takes its *own* whole-type
            // code and is nobody's instantiation…
            let closed = e.el.respell_ty(&e.cx, &flat).expect("`Flat` has a code");
            let Type::El { tm, .. } = &closed else { panic!("a reference") };
            assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("Flat").tag)));
            assert!(e.el.gen_app_of(tm).is_none());
            // …and a fieldless shape with no tag read declines outright.
            assert!(
                e.el.respell_ty(&e.cx, &Type::Unit { level: Level::Zero })
                    .is_none()
            );
            // The two look-alikes' own instantiations name different definitions,
            // which is the whole of the nominal guarantee.
            let (b2, _) = instance(&e, "Box2", &[(flat, fl)]);
            assert_ne!(
                e.el.respell_ty(&e.cx, &b1),
                e.el.respell_ty(&e.cx, &b2),
                "structurally identical instantiations take their own names"
            );
        }

        #[test]
        fn a_nested_instantiation_composes_the_references() {
            let e = env();
            let (flat, fl) = e.lowered("Flat");
            let (inner, il) = instance(&e, "Box", &[(flat, fl)]);
            let (outer, ol) = instance(&e, "Box", &[(inner, il)]);
            let r = e.el.respell_ty(&e.cx, &outer).expect("`Box<Box<Flat>>` respells");
            let Type::El { tm, .. } = &r else { panic!("a reference") };
            let (key, args) = e.el.gen_app_of(tm).expect("an application");
            assert_eq!(key, GenDef::TyCodeFn(e.ind("Box").tag));
            // The argument is itself a reference — `code_of` of an `El` is the
            // identity, so nothing is quoted twice (§3).
            let (inner_key, _) = e.el.gen_app_of(&args[0]).expect("the argument is an application");
            assert_eq!(inner_key, GenDef::TyCodeFn(e.ind("Box").tag));
            assert!(e.el.conv_types(&e.cx, &r, &outer, &ol));
            assert!(e.el.conv_types(&e.cx, &outer, &r, &ol));
            assert_eq!(e.el.whnf(&e.cx, &r, SPAN).expect("whnf"), outer);
        }

        #[test]
        fn an_open_instance_under_a_binder_shifts_as_a_unit() {
            // Axis 2 of `docs/testing-generated-terms.md`, and the one that
            // catches a depth error: the argument mentions a binder, so the
            // reference is minted *at* that depth rather than minted closed
            // and shifted (§4.1).
            let e = env();
            let mut cx = Cx::empty();
            cx.push("#A".into(), Type::Ty(Level::Zero), Level::succ(Level::Zero));
            let a = Type::El {
                level: Level::Zero,
                tm: Rc::new(Term::Var(LocalVar(0))),
            };
            let (open, ol) = e
                .el
                .lower_instance(&cx, &e.ind("Box"), &[(a, Level::Zero)], &[], SPAN)
                .expect("`Box<A>` lowers openly");
            let r = e.el.annotation_type(&cx, &open, 0);
            assert!(
                e.el
                    .kernel_check_type(&e.el.psi, heather_kernel::layer::Layer::Prog, &cx.gamma, &r, &ol)
                    .is_ok(),
                "the open reference typechecks in that context: {r:?}"
            );
            assert!(e.el.conv_types(&cx, &r, &open, &ol));
            assert!(e.el.conv_types(&cx, &open, &r, &ol));
            assert_eq!(e.el.whnf(&cx, &r, SPAN).expect("whnf"), open);
            // Tail and argument move together.
            let deeper = r.shift_local(1);
            assert_ne!(deeper, r);
            // …and the same instance one binder further in respells to that.
            assert_eq!(
                e.el.annotation_type(&cx, &open.shift_local(1), 1),
                deeper
            );
        }

        #[test]
        fn a_higher_level_instantiation_declines_and_stays_inline() {
            // §2.1's boundary: one definition, one level profile. A `Ty 1`
            // argument fails the guard's level comparison and keeps today's
            // spelling — a decline, never a wrong reference.
            let e = env();
            let one = Level::succ(Level::Zero);
            let mut cx = Cx::empty();
            cx.push("#A".into(), Type::Ty(one.clone()), Level::succ(one.clone()));
            let a = Type::El {
                level: one.clone(),
                tm: Rc::new(Term::Var(LocalVar(0))),
            };
            let (open, _) = e
                .el
                .lower_instance(&cx, &e.ind("Box"), &[(a, one)], &[], SPAN)
                .expect("`Box<A>` lowers at level 1 too");
            assert!(
                e.el.respell_ty(&cx, &open).is_none(),
                "a level-1 instantiation keeps the inline spelling"
            );
        }

        // -- emission: real source, the four axes ---------------------------

        #[test]
        fn annotation_types_name_closed_instances_and_preserve_plain_types() {
            let e = env();
            assert_eq!(e.el.annotation_type(&e.cx, &Type::Nat, 0), Type::Nat);
            let (flat, fl) = e.lowered("Flat");
            let named = e.el.annotation_type(&e.cx, &flat, 0);
            let Type::El { tm, .. } = &named else { panic!("closed code") };
            assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("Flat").tag)));
            let (boxed, level) = instance(&e, "Box", &[(flat, fl)]);
            let named = e.el.annotation_type(&e.cx, &boxed, 0);
            let Type::El { tm, .. } = &named else { panic!("instance code") };
            assert_eq!(e.el.gen_app_of(tm).map(|(key, _)| key),
                Some(GenDef::TyCodeFn(e.ind("Box").tag)));
            assert_eq!(e.el.annotation_type(&e.cx, &named, 0), named);
            assert!(e.el.conv_types(&e.cx, &named, &boxed, &level));
        }

        #[test]
        fn a_parameterized_child_projection_has_a_named_motive() {
            let e = env();
            let mut cx = Cx::empty();
            cx.push("A".into(), Type::Ty(Level::Zero), Level::succ(Level::Zero));
            let a = Type::El { level: Level::Zero, tm: Rc::new(Term::Var(LocalVar(0))) };
            let ind = e.ind("Box");
            let (boxed, level) = e.el.lower_instance(&cx, &ind, &[(a, Level::Zero)], &[], SPAN)
                .expect("open Box<A>");
            cx.push("b".into(), boxed.clone(), level.clone());
            let boxed = boxed.shift_local(1);
            let b = Rc::new(Term::Var(LocalVar(0)));
            let projection = e.el.child_projection(&cx, &ind, &boxed, &level,
                1, 0, Rc::clone(&b), (*b).clone(), SPAN).expect("child projection");
            let Term::ElimWf { motive, .. } = &projection else { panic!("recursive projection") };
            let Type::El { tm, .. } = &**motive else { panic!("named motive") };
            assert_eq!(e.el.gen_app_of(tm).map(|(key, _)| key),
                Some(GenDef::TyCodeFn(ind.tag)));
            e.el.kernel_check_term(&e.el.psi, heather_kernel::layer::Layer::Prog,
                &cx.gamma, &projection, &boxed, &level).expect("open neutral projection checks");
        }

        #[test]
        fn children_annotations_name_both_the_container_and_varying_payload() {
            for width in [2, 8, 32] {
                let mut e = env();
                let fields = (0..width).map(|i| format!("f{i}: Nat"))
                    .collect::<Vec<_>>().join(", ");
                e.el.elab_source(&format!("inductive Payload {{ P0, P1({fields}), P2 }}"))
                    .expect("payload declaration");
                let before = e.el.psi.bindings.len();
                e.el.elab_source(
                    "fn probe(b: Box<Payload>) -> Nat { match b { BNil => 0, BCons(a, r) => Succ(probe(r)) } }",
                ).expect("recursive match");
                let GlobalBinding::Tm { body: Some(body), .. } = e.el.psi.bindings.last().unwrap()
                    else { panic!("function body") };
                let Term::Lam { body, .. } = &**body else { panic!("parameter") };
                let Term::ElimWf { step, .. } = &**body else { panic!("match") };
                let Some((fun, _)) = crate::spelling::app_of(step) else { panic!("apply ih") };
                // Since `docs/app-by-head-type-design.md` the application is
                // `app@` and carries no annotation to copy a payload into; the
                // children vector's type is the case tree's motive's domain.
                let cs_ty = match &**fun {
                    Term::App { dom, .. } => Rc::clone(dom),
                    // The case tree's motive is `Π(cs : Vec(…)). …`.
                    Term::AppAt { fun: tree, .. } => {
                        let Term::Case { motive, .. } = &**tree else { panic!("a case tree") };
                        let Type::Pi { dom, .. } = &**motive else { panic!("its motive takes cs") };
                        Rc::clone(dom)
                    }
                    _ => panic!("apply children"),
                };
                let Type::Vec { elem, .. } = &*cs_ty else { panic!("children vector") };
                let Type::El { tm, .. } = &**elem else { panic!("named element") };
                let grew = (e.el.psi.bindings.len() - before) as u32;
                let (key, args) = e.el.gen_app_of(&tm.shift_global(grew)).expect("registered container");
                // Independent registry identities, never annotation_type(expected).
                assert_eq!(key, GenDef::TyCodeFn(e.ind("Box").tag));
                assert_eq!(args.len(), 1);
                assert!(e.el.is_gen_ref(&args[0], GenDef::TyCode(e.ind("Payload").tag)));
            }
        }

        #[test]
        fn a_parameterized_match_names_its_children_element_type() {
            let mut e = env();
            let before = e.el.psi.bindings.len();
            e.el.elab_source(
                "fn blen(b: Box<Flat>) -> Nat { match b { BNil => 0, BCons(a, r) => Succ(blen(r)) } }",
            ).expect("a match on an instantiated recursive type checks");
            let GlobalBinding::Tm { body: Some(body), .. } =
                e.el.psi.bindings.last().expect("a binding")
            else { panic!("a function body") };
            let Term::Lam { body, .. } = &**body else { panic!("one parameter") };
            let Term::ElimWf { step, .. } = &**body else { panic!("a recursive match") };
            // The step applies its case tree to cs and then ih. Inspect the
            // actual cs domain: an inline Wf here passes semantic tests but
            // copies every payload into each child-vector annotation.
            let Some((fun, _)) = crate::spelling::app_of(step) else { panic!("apply ih") };
            // Since `docs/app-by-head-type-design.md` the application is
            // `app@` and carries no annotation to copy a payload into; the
            // children vector's type is the case tree's motive's domain.
            let cs_ty = match &**fun {
                Term::App { dom, .. } => Rc::clone(dom),
                // The case tree's motive is `Π(cs : Vec(…)). …`.
                Term::AppAt { fun: tree, .. } => {
                    let Term::Case { motive, .. } = &**tree else { panic!("a case tree") };
                    let Type::Pi { dom, .. } = &**motive else { panic!("its motive takes cs") };
                    Rc::clone(dom)
                }
                _ => panic!("apply cs"),
            };
            let Type::Vec { elem, .. } = &*cs_ty else { panic!("children vector") };
            let Type::El { tm, .. } = &**elem else { panic!("named children element") };
            let grew = (e.el.psi.bindings.len() - before) as u32;
            assert_eq!(
                e.el.gen_app_of(&tm.shift_global(grew)).map(|(key, _)| key),
                Some(GenDef::TyCodeFn(e.ind("Box").tag)),
            );
            // Open element type, neutral and literal scrutinees, a checking
            // position, and a false equation on the same computation path.
            e.el.elab_source(
                "
fn bcopy<A>(b: Box<A>) -> Box<A> {
    match b { BNil => BNil, BCons(a, r) => BCons(a, bcopy(r)) }
}
theorem bcopy_open<A>(a: A): bcopy(BCons(a, BNil)) = BCons(a, BNil) { refl }
theorem blen_literal(): blen(BCons(FA, BCons(FB(2), BNil))) = 2 { refl }
",
            ).expect("the named telescope checks and computes at open and closed types");
            assert!(e.el.elab_source(
                "theorem bcopy_wrong(): bcopy(BCons(FA, BNil)) = BNil { refl }",
            ).is_err(), "a false computation must still be refused");
        }

        #[test]
        fn the_four_axes_on_a_monomorphized_container() {
            let mut e = env();
            e.el.elab_source(
                "
fn blen(b: Box<Flat>) -> Nat { match b { BNil => 0, BCons(a, r) => Succ(blen(r)) } }
fn bhead(b: Box<Flat>, d: Flat) -> Flat { match b { BNil => d, BCons(a, r) => a } }
fn bwrap<A>(a: A) -> Box<A> { BCons(a, BNil) }
fn bnest(f: Flat) -> Box<Box<Flat>> { BCons(BCons(f, BNil), BNil) }
theorem bhead_literal(): bhead(BCons(FB(1), BNil), FA) = FB(1) { refl }
theorem bhead_neutral(b: Box<Flat>, d: Flat): bhead(BCons(FA, b), d) = FA { refl }
theorem blen_computes(): blen(BCons(FA, BCons(FB(2), BNil))) = 2 { refl }
theorem bwrap_open(f: Flat): bhead(bwrap(f), FA) = f { refl }
",
            )
            .expect("the reference-spelled annotations check and compute");
            // Axis 4, on the same path.
            let r = e.el.elab_source(
                "theorem bhead_wrong(): bhead(BCons(FB(1), BNil), FA) = FA { refl }",
            );
            assert!(r.is_err(), "a false equation must still be refused");
        }

        #[test]
        fn a_value_indexed_instantiation_checks_and_computes() {
            let mut e = env();
            e.el.elab_source(
                "
fn bv0() -> BV(0) { BV([]) }
fn mflat(n: Nat, bits: [Nat; n]) -> Mixed<Flat>(n) { Mixed(FA, bits) }
theorem mflat_a(bits: [Nat; 2]): mflat(2, bits).a = FA { refl }
",
            )
            .expect("a value-indexed instantiation elaborates, checks and computes");
        }

        #[test]
        fn an_inferred_type_argument_discharges_the_reference() {
            // The chartered row (§1): an implicit type argument solved as a
            // *parameterized* instantiation is written into the whole spine's
            // annotations by `apply_implicit`'s discharge, and with a name for
            // it the kernel's own instantiation of the callee's codomain is
            // the same reference rather than a third spelling.
            let mut e = env();
            e.el.enable_emission_walk();
            e.el.elab_source(
                "
record Holder<M>(k: Nat) { item: M, tag: Nat, at: k = k }
fn mk_box(n: Nat) -> Box<Flat> { BCons(FB(n), BCons(FA, BNil)) }
fn hold(k: Nat) -> Holder<Box<Flat>>(k) { Holder(mk_box(k), k, refl) }
fn peek<M>(k: Nat, h: Holder<M>(k)) -> Nat { h.tag }
fn again<M>(k: Nat, h: Holder<M>(k), j: Nat) -> Nat { peek(k, h) }
fn chain(k: Nat) -> Nat { again(k, hold(k), peek(k, hold(k))) }
theorem chain_is_k(k: Nat): chain(k) = k { refl }
",
            )
            .expect("the inferred instantiation elaborates and computes");
            // `hold`'s statement names the instantiation the solution is:
            // the codomain is `El (app(Holder#tycode_fn^δ; …))`, and the
            // discharge writes that same term into the spine. (`Holder`'s
            // value parameter has to *occur* in the lowering for the matcher
            // to place it — §4.1's decline, and the reason `at: k = k` is
            // there.)
            let abs = e.el.lookup_global("hold").expect("`hold` is registered").abs as usize;
            let GlobalBinding::Tm { ty, .. } = e.el.psi.bindings.get(abs).expect("…and bound")
            else {
                panic!("a `fn` is a term binding")
            };
            let Type::Pi { cod, .. } = &**ty else { panic!("one parameter, one Π") };
            let Type::El { tm, .. } = &**cod else {
                panic!("the result is the reference, not the inline instance: {cod:?}")
            };
            let grew = (e.el.psi.bindings.len() - abs) as u32;
            assert_eq!(
                e.el.gen_app_of(&tm.shift_global(grew)).map(|(k, _)| k),
                Some(GenDef::TyCodeFn(e.ind("Holder").tag))
            );
            // …and the walker, which audits every emitted annotation slot,
            // finds nothing the chokepoint would have written differently —
            // including the slots the discharge filled.
            let findings = e.el.take_emission_findings();
            let listed: Vec<String> = findings
                .iter()
                .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                .collect();
            assert!(
                findings.is_empty(),
                "the emission walker is empty on the inferred chain:\n{}",
                listed.join("\n")
            );
        }

        // -- the stored template's own Ψ frame -------------------------------

        /// `docs/telescoped-record-projections-design.md` §2.1: a stored
        /// `TyCodeFn` is read through a rescoping, because it was computed
        /// before its own binding was pushed.
        mod stale_template {
            //! [`Elaborator::register_ty_code_fn`] computes the template and
            //! the statement, pushes `D#tycode_fn`, and commits them *as
            //! computed* — so both sit in the Ψ prefix before the definition's
            //! own binding, and `GlobalVar`s number from the end of Ψ. Every
            //! declaration pushed since has moved them, so the entry is read
            //! through a shift off the reference's own variable.
            //!
            //! Nothing the module above declares has a lowering that mentions
            //! a global — `Box`, `Two`, `Cell`, `BV`, `Mixed` lower to tags,
            //! `Σ`s, `Nat`s and `El (Var …)` — so for all of them the stale
            //! frame and today's frame are the same characters, which is
            //! exactly why the defect survived the device's own suite. Every
            //! declaration here mentions one.
            //!
            //! **The second half, and what these tests pin about it.** The
            //! shift alone is not enough: a template global also carries the
            //! *telescope's* own substitution tail (`u^{·^{|Θ|+d}}`) where the
            //! subject carries the use site's (`u^{·^{outer+d}}`), and
            //! comparing those syntactically is comparing the two contexts'
            //! lengths — so with the rescoping alone the match succeeded only
            //! at the identity spine (the telescope's own length, which is
            //! what `register_rec_projs` asks at) and declined at every
            //! ordinary use site. A *closed* global is the same constant in
            //! both frames and its tail says nothing about it, so `Holes::tm`
            //! compares the index; `instance_of_template` then composes the
            //! subject's frame into the copy the identity step checks, which
            //! is what keeps the answer scoped where the subject is rather
            //! than where the template was stored.

            use super::*;

            /// `Slot`'s `ok` field mentions the global `ident`, and it is
            /// declared after thirteen other declarations and a function.
            /// `Mimic` is the look-alike: the same spine, a different nominal
            /// tag.
            const EXTRA: &str = "
inductive Tok { TA, TB(n: Nat) }
fn ident(n: Nat) -> Nat { n }
record Slot<A> { item: A, n: Nat, ok: n = ident(n) }
record Mimic<A> { item: A, n: Nat, ok: n = ident(n) }
";

            fn env_with_globals() -> Env {
                let mut e = env();
                e.el
                    .elab_source(EXTRA)
                    .expect("the global-mentioning declarations elaborate");
                e
            }

            /// A context of exactly one binder — `Slot`'s own telescope
            /// length — and the type parameter as its `El (Var 0)`.
            fn telescope_cx() -> Cx {
                let mut cx = Cx::empty();
                cx.push("#A".into(), Type::Ty(Level::Zero), Level::succ(Level::Zero));
                cx
            }

            #[test]
            fn a_lowering_that_mentions_a_global_matches_its_own_reference() {
                let e = env_with_globals();
                let cx = telescope_cx();
                // Axis 2: an **open** element type, which is also the identity
                // spine `register_rec_projs` proves its record binder with.
                let a = Type::El {
                    level: Level::Zero,
                    tm: Rc::new(Term::Var(LocalVar(0))),
                };
                let (open, ol) = e
                    .el
                    .lower_instance(&cx, &e.ind("Slot"), &[(a, Level::Zero)], &[], SPAN)
                    .expect("`Slot<A>` lowers openly");
                let r = e.el.respell_ty(&cx, &open).expect(
                    "`Slot<A>` respells: the stored template is read into today's Ψ",
                );
                let Type::El { level, tm } = &r else {
                    panic!("the spelling is `El` of an application")
                };
                assert_eq!(*level, ol);
                let (key, args) = e.el.gen_app_of(tm).expect("an application of a definition");
                assert_eq!(key, GenDef::TyCodeFn(e.ind("Slot").tag));
                assert_eq!(args.len(), 1);
                // A spelling change and nothing else, with the registry's own
                // copy behind it — the `ident` inside that copy spelled for
                // the Ψ the reader is in.
                assert!(e.el.conv_types(&cx, &r, &open, &ol));
                assert!(e.el.conv_types(&cx, &open, &r, &ol));
                assert_eq!(e.el.unspell_here(&r).expect("the reference unspells"), open);
                assert_eq!(e.el.whnf(&cx, &r, SPAN).expect("whnf"), open);
                // A **closed** element type at the same spine, so the win is
                // not a property of the argument being a bare binder.
                let (flat, fl) = e.lowered("Flat");
                let (closed, cl) = instance(&e, "Slot", &[(flat.clone(), fl.clone())]);
                let here = closed.shift_local(1);
                let rc = e
                    .el
                    .respell_ty(&cx, &here)
                    .expect("`Slot<Flat>` respells at the telescope's own length");
                let Type::El { tm: ctm, .. } = &rc else { panic!("`El` of an application") };
                let (ckey, cargs) = e.el.gen_app_of(ctm).expect("an application");
                assert_eq!(ckey, GenDef::TyCodeFn(e.ind("Slot").tag));
                assert!(e.el.is_gen_ref(&cargs[0], GenDef::TyCode(e.ind("Flat").tag)));
                assert!(e.el.conv_types(&cx, &rc, &here, &cl));
                // The look-alike is a different declaration and gets its own
                // name; neither is the other's.
                let (mimic, _) = instance(&e, "Mimic", &[(flat, fl)]);
                let m = e
                    .el
                    .respell_ty(&cx, &mimic.shift_local(1))
                    .expect("`Mimic<Flat>` respells");
                let Type::El { tm: mtm, .. } = &m else { panic!("`El` of an application") };
                assert_eq!(
                    e.el.gen_app_of(mtm).map(|(k, _)| k),
                    Some(GenDef::TyCodeFn(e.ind("Mimic").tag))
                );
                assert_ne!(m, rc);
                // The negative control, and the one that pins the fix as a
                // *rescoping* rather than a matcher that stopped looking at
                // globals: the stale spelling itself — this lowering with its
                // `ident` pointing one binding over — is not this
                // instantiation and must decline.
                assert!(
                    e.el.respell_ty(&cx, &open.shift_global(1)).is_none(),
                    "a lowering whose global points one binding over is not this instance"
                );
            }

            #[test]
            fn the_axes_through_a_global_mentioning_record() {
                let mut e = env_with_globals();
                // A **checking** position through the record's own type at
                // every annotated result and every `refl`, an **open** element
                // type (`mkslot<A>`), a literal and a neutral receiver, and the
                // computation pinned rather than merely built
                // (`docs/testing-generated-terms.md`). This is the path the
                // rescoping widened; it has to keep checking and computing.
                e.el
                    .elab_source(
                        "
fn mkslot<A>(a: A, n: Nat) -> Slot<A> { Slot(a, n, refl) }
fn slot_n<A>(s: Slot<A>) -> Nat { s.n }
fn slot_flat(n: Nat) -> Slot<Flat> { mkslot(FA, n) }
theorem slot_open<A>(a: A, n: Nat): slot_n(mkslot(a, n)) = n { refl }
theorem slot_neutral<A>(s: Slot<A>): slot_n(mkslot(slot_n(s), 1)) = 1 { refl }
theorem slot_literal(): slot_n(slot_flat(2)) = 2 { refl }
",
                    )
                    .expect("the telescope checks and computes, open and closed");
                // Axis 4, on the same computation path.
                assert!(
                    e.el
                        .elab_source("theorem slot_wrong(): slot_n(slot_flat(2)) = 3 { refl }")
                        .is_err(),
                    "a false equation must still be refused"
                );
            }

            #[test]
            fn the_entry_is_read_through_the_references_own_variable() {
                let mut e = env_with_globals();
                // The entry's `stmt` *is* the definition's Ψ statement, so the
                // two independent reads — the rescoped entry and
                // `rec_proj_ref_at`'s read of the binding off the reference's
                // own variable — must be one term, at every Ψ length.
                fn both_reads_agree(e: &Env) {
                    for name in ["Box", "Two", "Box2", "BV", "Mixed", "Cell", "Slot", "Mimic"] {
                        let tag = e.ind(name).tag;
                        let key = GenDef::TyCodeFn(tag);
                        let entry = e.el.ty_code_fn_now(tag, 0).expect("a registered entry");
                        let fun = e.el.gen_ref(&e.cx, key).expect("a reference");
                        let Term::GlobalTm { var, .. } = &fun else {
                            panic!("a definition reference is a global")
                        };
                        let abs = *e.el.types.gdefs().abs_for(&key).expect("an index") as usize;
                        let GlobalBinding::Tm { ty, .. } =
                            e.el.psi.bindings.get(abs).expect("…and bound")
                        else {
                            panic!("a definition is a term binding")
                        };
                        assert_eq!(
                            *entry.stmt,
                            ty.shift_global(var.0 + 1),
                            "`{name}`'s entry and its Ψ binding disagree"
                        );
                        // Read at the frame it was stored in — the prefix
                        // before its own binding — the rescoping is the
                        // identity. That is what makes a replayed image
                        // self-correct instead of needing a codec change.
                        let raw = e.el.ty_code_fn_at(tag, abs as u32).expect("a registered entry");
                        assert_eq!(*raw.stmt, **ty, "`{name}`'s entry is stored unshifted");
                    }
                }
                let open_slot = |e: &Env| {
                    let cx = telescope_cx();
                    let a = Type::El {
                        level: Level::Zero,
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    };
                    let (open, _) = e
                        .el
                        .lower_instance(&cx, &e.ind("Slot"), &[(a, Level::Zero)], &[], SPAN)
                        .expect("`Slot<A>` lowers openly");
                    (cx, open)
                };
                both_reads_agree(&e);
                let (cx, open) = open_slot(&e);
                assert!(e.el.respell_ty(&cx, &open).is_some());
                // …and again after several more pushes, which is the whole
                // point: a stored copy is stale from the next push on.
                e.el
                    .elab_source(
                        "
inductive Later { LA, LB(n: Nat) }
fn later(n: Nat) -> Nat { n }
record Third<A> { a: A, n: Nat, ok: n = later(n) }
",
                    )
                    .expect("more declarations elaborate");
                both_reads_agree(&e);
                let (cx, open) = open_slot(&e);
                assert!(
                    e.el.respell_ty(&cx, &open).is_some(),
                    "the entry is read off today's Ψ, not the one it was stored in"
                );
                // The **tail** half, landed 2026-09-15 (implementation pass 2):
                // a template global carries the telescope's own substitution
                // tail (`u^{·^{|Θ|+d}}`) and the subject's carries the use
                // site's (`u^{·^{outer+d}}`), so comparing them syntactically
                // compared the two contexts' lengths and declined everywhere
                // but the identity spine. `Holes::tm` compares a *closed*
                // global by its index, and `instance_of_template` composes the
                // subject's own frame into the copy step 2 checks — so the
                // same instantiation is recovered at any outer depth, and the
                // spelling it produces is scoped where the subject is.
                let closed = instance(&e, "Slot", &[e.lowered("Flat")]).0;
                let at0 = e
                    .el
                    .respell_ty(&Cx::empty(), &closed)
                    .expect("a closed instantiation respells from the empty context");
                assert!(e.el.conv_types(&Cx::empty(), &at0, &closed, &Level::Zero));
                // …and from a context of a different length, which is the
                // shape every ordinary use site has. The reference is the same
                // one, weakened: the arguments are closed, so only the
                // substitution tails' lengths move.
                let mut deep = Cx::empty();
                deep.push("#a".into(), Type::Nat, Level::Zero);
                deep.push("#b".into(), Type::Nat, Level::Zero);
                let at2 = e
                    .el
                    .respell_ty(&deep, &closed.shift_local(2))
                    .expect("…and at outer depth 2");
                assert_eq!(
                    at2,
                    at0.shift_local(2),
                    "the same instantiation must respell to the same reference at every depth"
                );
            }
        }

        // -- §13: projections at an instantiation ---------------------------

        /// A context holding one receiver of the closed type `ty`, and the
        /// receiver itself — as a **chain** (`fst` of a pair whose first
        /// component is `ty`), because the boundary keeps the inline walk at a
        /// *bare* binder and takes the reference at a chain
        /// (`docs/x86-scaling-rail-out-of-fuel-design.md` §2.5). These probes
        /// are about the reference, so they hold one.
        fn receiver(ty: &Type, l: &Level) -> (Cx, Rc<Term>) {
            let mut cx = Cx::empty();
            let unit = || Rc::new(Type::Unit { level: Level::Zero });
            cx.push(
                "#v".into(),
                Type::Sigma {
                    fst_level: l.clone(),
                    snd_level: Level::Zero,
                    fst: Rc::new(ty.clone()),
                    snd: unit(),
                },
                Level::max(l.clone(), Level::Zero),
            );
            // The receiver lives *inside* `cx`, so its annotations are at
            // that depth while the binder's own type is not.
            (
                cx,
                Rc::new(Term::Fst {
                    fst_level: l.clone(),
                    snd_level: Level::Zero,
                    fst_ty: Rc::new(ty.shift_local(1)),
                    snd_ty: unit(),
                    pair: Rc::new(Term::Var(LocalVar(0))),
                }),
            )
        }

        #[test]
        fn a_telescoped_records_projections_get_names_and_a_closed_flat_one_does_not() {
            let e = env();
            // §13's telescoped boundary: a record over a telescope whose
            // spine is **not** dependent is named, because the reason to name
            // there is the receiver's *reference* and not the spine's
            // exponent — and its definitions write the tail out, which is
            // what a dependent spine may not do (§13.6).
            for name in ["Cell", "Mixed", "BV"] {
                assert!(
                    e.el.gen_ref(&e.cx, GenDef::RecProj(e.ind(name).tag, 0))
                        .is_some(),
                    "`{name}` is telescoped and flat: its field 0 should have a `#proj`"
                );
            }
            // `Dep<A>(n)`'s spine **is** dependent, and since
            // `docs/telescoped-record-projections-design.md` §3 that is the
            // fourth cell rather than a decline: the closed triple with the
            // declaration's own `Θ` in front. The tail family is the
            // discriminator — the simple telescoped device writes its tails
            // out and registers none.
            for (name, fam) in [("Dep", true), ("Cell", false), ("Mixed", false), ("BV", false)] {
                assert!(
                    e.el.gen_ref(&e.cx, GenDef::RecProj(e.ind(name).tag, 0))
                        .is_some(),
                    "`{name}` should have a `#proj` for field 0"
                );
                assert_eq!(
                    e.el.gen_ref(&e.cx, GenDef::RecFam(e.ind(name).tag, 0))
                        .is_some(),
                    fam,
                    "`{name}`'s shape is decided by its spine's dependency"
                );
                assert_eq!(e.el.rec_projs_are_dependent(e.ind(name).tag), fam);
            }
            // …and the closed side is exactly as it was: a dependent spine is
            // named, a flat one is left to the (already linear) walk.
            assert!(
                e.el.gen_ref(&e.cx, GenDef::RecProj(e.ind("DepC").tag, 0))
                    .is_some()
            );
            assert!(
                e.el.gen_ref(&e.cx, GenDef::RecProj(e.ind("Plain").tag, 0))
                    .is_none(),
                "a closed non-dependent record keeps the inline walk"
            );
        }

        #[test]
        fn a_field_read_at_an_instance_is_the_application() {
            let e = env();
            let (flat, fl) = e.lowered("Flat");
            let (flat2, fl2) = e.lowered("Flat2");
            let (inline, il) = e
                .el
                .lower_instance(
                    &e.cx,
                    &e.ind("Cell"),
                    &[(flat, fl), (flat2.clone(), fl2)],
                    &[],
                    SPAN,
                )
                .expect("`Cell<Flat, Flat2>` lowers");
            // The receiver's own type is the reference, which is what a
            // binder respelled by §4.1 carries.
            let r = e.el.respell_ty(&e.cx, &inline).expect("the instance respells");
            let (cx, v) = receiver(&r, &il);
            let (tm, ty, lvl) = e
                .el
                .project_field(&cx, &e.ind("Cell"), &r.shift_local(1), Rc::clone(&v), 1, SPAN)
                .expect("the field reads");
            // Structural: the telescope's arguments, then the receiver.
            let (key, args) = e.el.gen_app_of(&tm).expect("an application of a definition");
            assert_eq!(key, GenDef::RecProj(e.ind("Cell").tag, 1));
            assert_eq!(args.len(), 3, "two type arguments and the receiver");
            assert_eq!(*args[2], *v);
            // It checks in that context, and its type is the field's.
            e.el.kernel_check_term(
                &e.el.psi,
                heather_kernel::layer::Layer::Prog,
                &cx.gamma,
                &tm,
                &ty,
                &lvl,
            )
            .expect("the applied projection typechecks");
            assert!(e.el.conv_types(&cx, &ty, &flat2.shift_local(1), &lvl));
            // …and the *other* route of `instance_args` (§13.4) agrees: the
            // same field of the same value, read off the inline spelling, so
            // the hole-match and the reference's own spine recover one `ā`.
            let (inline_tm, inline_ty, inline_lvl) = e
                .el
                .project_field(
                    &cx,
                    &e.ind("Cell"),
                    &inline.shift_local(1),
                    Rc::clone(&v),
                    1,
                    SPAN,
                )
                .expect("the inline read");
            assert!(e.el.conv_types(&cx, &ty, &inline_ty, &inline_lvl));
            // …and each is the other's term at the other's type, which is the
            // conservativity claim the kernel decides — and which would fail
            // if either route recovered different arguments.
            for (t, at, al) in [(&tm, &inline_ty, &inline_lvl), (&inline_tm, &ty, &lvl)] {
                e.el.kernel_check_term(
                    &e.el.psi,
                    heather_kernel::layer::Layer::Prog,
                    &cx.gamma,
                    t,
                    at,
                    al,
                )
                .expect("the named projection and the inline walk agree");
            }
        }

        #[test]
        fn a_wrong_instance_application_is_refused() {
            // Axis 4. The definition's domain at `ā` *is* the instantiation,
            // so a receiver from a different one is a kernel rejection rather
            // than a silently wrong annotation.
            let e = env();
            let (flat, fl) = e.lowered("Flat");
            let (flat2, fl2) = e.lowered("Flat2");
            let (inline, il) = e
                .el
                .lower_instance(
                    &e.cx,
                    &e.ind("Cell"),
                    &[(flat.clone(), fl.clone()), (flat2.clone(), fl2.clone())],
                    &[],
                    SPAN,
                )
                .expect("`Cell<Flat, Flat2>` lowers");
            let r = e.el.respell_ty(&e.cx, &inline).expect("respells");
            let (cx, v) = receiver(&r, &il);
            // The *swapped* instantiation's arguments, against this receiver.
            let (swapped, _) = e
                .el
                .lower_instance(&e.cx, &e.ind("Cell"), &[(flat2, fl2), (flat, fl)], &[], SPAN)
                .expect("`Cell<Flat2, Flat>` lowers");
            let args =
                e.el.instance_args(&cx, &e.ind("Cell"), &swapped.shift_local(1))
                    .expect("the swapped instantiation's arguments");
            let (tm, ty, lvl) =
                e.el.rec_proj_ref_at(&cx, e.ind("Cell").tag, 1, &args, &v)
                    .expect("the spine is built — it is the kernel that refuses it");
            assert!(
                e.el.kernel_check_term(
                    &e.el.psi,
                    heather_kernel::layer::Layer::Prog,
                    &cx.gamma,
                    &tm,
                    &ty,
                    &lvl,
                )
                .is_err(),
                "a wrong-instance receiver must not typecheck"
            );
        }

        #[test]
        fn a_projection_under_a_binder_shifts_as_a_unit() {
            // Axis 2: an *open* element type. The instantiation's argument is
            // a binder the walk has crossed, so the whole spine — head tail,
            // arguments and receiver — has to move together.
            let e = env();
            let (flat, fl) = e.lowered("Flat");
            let mut acx = Cx::empty();
            acx.push("#A".into(), Type::Ty(Level::Zero), Level::succ(Level::Zero));
            let a = Type::El {
                level: Level::Zero,
                tm: Rc::new(Term::Var(LocalVar(0))),
            };
            let (open, ol) = e
                .el
                .lower_instance(
                    &acx,
                    &e.ind("Cell"),
                    &[(a, Level::Zero), (flat.shift_local(1), fl)],
                    &[],
                    SPAN,
                )
                .expect("`Cell<A, Flat>` lowers openly");
            let r = e.el.respell_ty(&acx, &open).expect("the open instance respells");
            let mut cx = acx.clone();
            // A chain, not the bare binder — the boundary keeps the walk at a
            // bare `Var` (`docs/x86-scaling-rail-out-of-fuel-design.md` §2.5).
            let unit = || Rc::new(Type::Unit { level: Level::Zero });
            cx.push(
                "#v".into(),
                Type::Sigma {
                    fst_level: ol.clone(),
                    snd_level: Level::Zero,
                    fst: Rc::new(r.clone()),
                    snd: unit(),
                },
                Level::max(ol.clone(), Level::Zero),
            );
            let v: Rc<Term> = Rc::new(Term::Fst {
                fst_level: ol.clone(),
                snd_level: Level::Zero,
                fst_ty: Rc::new(r.shift_local(1)),
                snd_ty: unit(),
                pair: Rc::new(Term::Var(LocalVar(0))),
            });
            let (tm, ty, lvl) = e
                .el
                .project_field(&cx, &e.ind("Cell"), &r.shift_local(1), v, 0, SPAN)
                .expect("the open field reads");
            e.el.kernel_check_term(
                &e.el.psi,
                heather_kernel::layer::Layer::Prog,
                &cx.gamma,
                &tm,
                &ty,
                &lvl,
            )
            .expect("the open applied projection typechecks in that context");
            // The field is the parameter, at this depth.
            assert!(e.el.conv_types(
                &cx,
                &ty,
                &Type::El {
                    level: Level::Zero,
                    tm: Rc::new(Term::Var(LocalVar(1))),
                },
                &lvl
            ));
            let deeper = tm.shift_local(1);
            assert_ne!(deeper, tm);
            let (_, args) = e.el.gen_app_of(&deeper).expect("still an application");
            assert_eq!(args.len(), 3);
        }

        #[test]
        fn the_four_axes_on_telescoped_field_reads() {
            // Emission, on real source: literal and neutral receivers, an open
            // element type, a *checking* position (the annotated `fn` results),
            // a dependent field type, and a false equation refused.
            let mut e = env();
            e.el.enable_emission_walk();
            e.el.elab_source(
                "
fn cl(c: Cell<Flat, Flat2>) -> Flat { c.l }
fn cr(c: Cell<Flat, Flat2>) -> Flat2 { c.r }
fn copen<A, B>(c: Cell<A, B>) -> A { c.l }
fn cnest(c: Cell<Cell<Flat, Flat2>, Flat>) -> Flat2 { c.l.r }
fn mkdep<A>(n: Nat, a: A) -> Dep<A>(n) { Dep(n, refl, a) }
fn dk<A>(n: Nat, d: Dep<A>(n)) -> Nat { d.k }
fn da<A>(n: Nat, d: Dep<A>(n)) -> A { d.a }
fn dsame<A>(n: Nat, d: Dep<A>(n)) -> d.k = n { d.same }
theorem cl_literal(): cl(Cell(FA, GB(1))) = FA { refl }
theorem cr_literal(): cr(Cell(FA, GB(1))) = GB(1) { refl }
theorem cl_neutral(c: Cell<Flat, Flat2>): cl(Cell(FA, c.r)) = FA { refl }
theorem copen_open(f: Flat, g: Flat2): copen(Cell(f, g)) = f { refl }
theorem cnest_computes(): cnest(Cell(Cell(FA, GB(2)), FB(3))) = GB(2) { refl }
theorem dk_computes(a: Flat): dk(3, mkdep(3, a)) = 3 { refl }
theorem da_computes(a: Flat): da(3, mkdep(3, a)) = a { refl }
",
            )
            .expect("telescoped field reads elaborate, check and compute");
            let r = e.el.elab_source(
                "theorem cl_wrong(): cl(Cell(FA, GB(1))) = FB(1) { refl }",
            );
            assert!(r.is_err(), "a false equation must still be refused");
            // Every emitted annotation slot is one the chokepoint would have
            // written the same way (§12 item 6).
            let findings = e.el.take_emission_findings();
            let listed: Vec<String> = findings
                .iter()
                .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                .collect();
            assert!(
                findings.is_empty(),
                "the emission walker is empty on telescoped field reads:\n{}",
                listed.join("\n")
            );
        }

        #[test]
        fn the_reference_is_minted_at_a_chain_and_not_at_a_binder() {
            // `docs/x86-scaling-rail-out-of-fuel-design.md` §2.5: the boundary
            // is on shapes that survive substitution. A bare binder is exactly
            // what a use site replaces, so it keeps the walk; a chain over one
            // is §13.1's measured payer and keeps the reference; a computed
            // receiver is §13.10's refusal and stays out.
            let g = || Term::GlobalTm {
                var: GlobalVar(0),
                subst: LocalSubst::id(&LocalCtx::nil()),
            };
            let app = |fun: Term, arg: Term| Term::App {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Ty(Level::Zero)),
                cod: Rc::new(Type::Ty(Level::Zero)),
                fun: Rc::new(fun),
                arg: Rc::new(arg),
            };
            let snd = |pair: Term| Term::Snd {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst_ty: Rc::new(Type::Ty(Level::Zero)),
                snd_ty: Rc::new(Type::Ty(Level::Zero)),
                pair: Rc::new(pair),
            };
            let x = || Term::Var(LocalVar(0));
            let admits = crate::inductive::receiver_admits_reference;
            assert!(!admits(&x()), "a bare binder keeps the walk");
            assert!(admits(&snd(x())), "a chain over a binder takes the reference");
            assert!(admits(&app(x(), x())), "an applied local is still a chain");
            // A computed receiver, one layer or many: §13.10's refusal.
            assert!(!admits(&app(g(), x())));
            assert!(!admits(&app(g(), app(g(), x()))));
            assert!(!admits(&snd(app(g(), x()))));
        }

        #[test]
        fn a_record_field_type_and_its_use_site_spell_a_computed_receiver_alike() {
            // The x86 rail's shape in a dozen lines
            // (`docs/x86-scaling-rail-out-of-fuel-design.md` §1): a record
            // whose later field type reads a field of an **earlier** one,
            // constructed at a *computed* state — so the declaration's
            // declaration's spelling meets a global-headed receiver while the
            // accompanying theorem states the same read directly.
            //
            // The four axes of `docs/testing-generated-terms.md`: a neutral
            // receiver (`pack`) and a literal one (`pack_lit`, whose argument
            // is *not* neutral, so the boundary declines and the inline walk
            // must still be right), an **open** element type (`A`, `B`), a
            // **checking** position (each `Pack(…)`'s second field is checked
            // against the substituted field type), and a negative control.
            let mut e = env();
            e.el.enable_emission_walk();
            e.el.elab_source(
                "
fn bump<A, B>(c: Cell<A, B>) -> Cell<A, B> { Cell(c.l, c.r) }
record Pack<A, B>(seed: Cell<A, B>) {
    out: Cell<A, B>,
    same_r: out.r = seed.r,
}
theorem bump_keeps_r<A, B>(c: Cell<A, B>): bump(c).r = c.r { refl }
fn pack<A, B>(c: Cell<A, B>) -> Pack<A, B>(c) { Pack(bump(c), bump_keeps_r(c)) }
fn pack_lit() -> Pack<Flat, Flat2>(Cell(FA, GB(1))) {
    Pack(bump(Cell(FA, GB(1))), bump_keeps_r(Cell(FA, GB(1))))
}
theorem pack_out_r<A, B>(c: Cell<A, B>): pack(c).out.r = c.r { pack(c).same_r }
theorem pack_lit_out_r(): pack_lit().out.r = GB(1) { refl }
",
            )
            .expect("a record field type over a computed receiver checks");
            // Negative control, at the *same* type on both sides so it is a
            // refuted equation and not a mismatched one.
            let r = e.el.elab_source(
                "theorem pack_wrong<A>(c: Cell<A, Flat2>): bump(c).r = GA { refl }",
            );
            assert!(r.is_err(), "a false equation must still be refused");
            let r = e.el.elab_source(
                "theorem pack_lit_wrong(): pack_lit().out.r = GB(2) { refl }",
            );
            assert!(r.is_err(), "a false literal equation must still be refused");
            let findings = e.el.take_emission_findings();
            let listed: Vec<String> = findings
                .iter()
                .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                .collect();
            assert!(
                findings.is_empty(),
                "the emission walker is empty on a computed receiver:\n{}",
                listed.join("\n")
            );
        }

        // -- the dependent telescoped device --------------------------------

        /// `docs/telescoped-record-projections-design.md` §3/§4: the fourth
        /// cell of the projection table — the closed `recfam`/`proj`/`tail`
        /// triple with the declaration's own `Θ` in front — and §2.2/§2.3's
        /// two extensions to the hole matcher, which are its prerequisites.
        mod dependent_telescope {
            //! `Dep<A>(n) { k, same: k = n, a: A }` is the module's telescoped
            //! *dependent* record, and until 2026-09-15 it was the one cell
            //! `register_rec_projs` declined — so every field read off every
            //! record in `lib/std/parser` was `project_field`'s inline
            //! `fst(sndʲ v)` walk with its tail-substitution exponent.
            //!
            //! The four axes of `docs/testing-generated-terms.md` are varied
            //! here rather than asserted once: a **literal** receiver (an
            //! assembled record value) and a **neutral** one (a parameter, and
            //! a **bare binder**, which §4 newly admits); an **open** element
            //! type, so nothing is fixed by the declaration; a **checking**
            //! position — the projected field as the proof of a stated
            //! theorem, so a wrong type is a rejection and not a different
            //! term; and three negatives, the last of which is refused by the
            //! kernel rather than by a guard.

            use super::*;

            fn nat(n: u32) -> Term {
                let mut t = Term::Zero;
                for _ in 0..n {
                    t = Term::Succ(Rc::new(t));
                }
                t
            }

            /// `Dep<Flat>(n)` as `lower_instance` writes it, and its level.
            fn dep_at(e: &Env, n: u32) -> (Type, Level) {
                let (flat, fl) = e.lowered("Flat");
                e.el.lower_instance(
                    &e.cx,
                    &e.ind("Dep"),
                    &[(flat, fl)],
                    &[(nat(n), Type::Nat, Level::Zero)],
                    SPAN,
                )
                .expect("`Dep<Flat>(n)` lowers")
            }

            #[test]
            fn a_dependent_telescope_registers_the_closed_triple_over_its_own_theta() {
                let e = env();
                let tag = e.ind("Dep").tag;
                // Three definitions per spine entry and one more for the tag's
                // own entry: `3·nfields + 1` (§7), which is what the
                // `psi().bindings.len()` fixtures move by.
                for j in 0..3 {
                    assert!(
                        e.el.gen_ref(&e.cx, GenDef::RecProj(tag, j)).is_some(),
                        "field {j} is named"
                    );
                }
                for step in 0..=3 {
                    assert!(
                        e.el.gen_ref(&e.cx, GenDef::RecFam(tag, step)).is_some(),
                        "spine entry {step} has a tail family"
                    );
                }
                for step in 1..3 {
                    assert!(e.el.gen_ref(&e.cx, GenDef::RecTail(tag, step)).is_some());
                }
                // The statement is over the telescope: two arguments before
                // the receiver, and the domain at them is the receiver's own
                // *reference* (§13.2's load-bearing choice, unchanged).
                let (inline, il) = dep_at(&e, 3);
                let r = e.el.respell_ty(&e.cx, &inline).expect("the instance respells");
                let (cx, v) = receiver(&r, &il);
                let (tm, ty, lvl) = e
                    .el
                    .project_field(&cx, &e.ind("Dep"), &r.shift_local(1), Rc::clone(&v), 2, SPAN)
                    .expect("the last field reads");
                let (key, args) = e.el.gen_app_of(&tm).expect("an application of a definition");
                assert_eq!(key, GenDef::RecProj(tag, 2));
                assert_eq!(args.len(), 3, "one type argument, one value argument, the receiver");
                assert_eq!(*args[2], *v);
                e.el.kernel_check_term(
                    &e.el.psi,
                    heather_kernel::layer::Layer::Prog,
                    &cx.gamma,
                    &tm,
                    &ty,
                    &lvl,
                )
                .expect("the applied projection typechecks");
                // …and it is the inline walk's term at the inline walk's type,
                // which is the conservativity the kernel decides.
                let (wtm, wty, wlvl) = e
                    .el
                    .project_field(&cx, &e.ind("Dep"), &inline.shift_local(1), v, 2, SPAN)
                    .expect("the inline read");
                for (t, at, al) in [(&tm, &wty, &wlvl), (&wtm, &ty, &lvl)] {
                    e.el.kernel_check_term(
                        &e.el.psi,
                        heather_kernel::layer::Layer::Prog,
                        &cx.gamma,
                        t,
                        at,
                        al,
                    )
                    .expect("the named projection and the inline walk agree");
                }
            }

            #[test]
            fn the_dependent_device_fires_at_a_bare_binder_and_the_simple_one_does_not() {
                // §4: the gate is a real trade only where the alternative is
                // linear. `close_body`'s reads are all off bare binders, so
                // keeping it for the dependent cell would register every
                // definition the parser needs and use none of them.
                let e = env();
                let named = |name: &str, idx: usize| {
                    let (inline, il) = if name == "Dep" {
                        dep_at(&e, 3)
                    } else {
                        let (flat, fl) = e.lowered("Flat");
                        let (flat2, fl2) = e.lowered("Flat2");
                        e.el.lower_instance(
                            &e.cx,
                            &e.ind("Cell"),
                            &[(flat, fl), (flat2, fl2)],
                            &[],
                            SPAN,
                        )
                        .expect("`Cell<Flat, Flat2>` lowers")
                    };
                    let r = e.el.respell_ty(&e.cx, &inline).expect("respells");
                    let mut cx = Cx::empty();
                    cx.push("#v".into(), r.clone(), il.clone());
                    let bare: Rc<Term> = Rc::new(Term::Var(LocalVar(0)));
                    let (tm, ..) = e
                        .el
                        .project_field(&cx, &e.ind(name), &r.shift_local(1), bare, idx, SPAN)
                        .expect("the bare-binder read elaborates either way");
                    e.el.gen_app_of(&tm).map(|(k, _)| k)
                };
                assert_eq!(
                    named("Dep", 0),
                    Some(GenDef::RecProj(e.ind("Dep").tag, 0)),
                    "the dependent device is exempt from the receiver gate"
                );
                assert_eq!(
                    named("Cell", 0),
                    None,
                    "the non-dependent telescoped device keeps the gate verbatim"
                );
            }

            #[test]
            fn a_wrong_instance_dependent_projection_is_refused_by_the_kernel() {
                // The control that says the reference means what it claims:
                // `D#projⱼ` at the *wrong* `ā`. The spine is built — nothing
                // here guards it — and the kernel refuses it, because the
                // definition's domain at `ā` is the instantiation itself.
                let e = env();
                let (inline, il) = dep_at(&e, 3);
                let r = e.el.respell_ty(&e.cx, &inline).expect("respells");
                let (cx, v) = receiver(&r, &il);
                let (other, _) = dep_at(&e, 4);
                let args =
                    e.el.instance_args(&cx, &e.ind("Dep"), &other.shift_local(1))
                        .expect("`Dep<Flat>(4)`'s arguments are recovered");
                let (tm, ty, lvl) =
                    e.el.rec_proj_ref_at(&cx, e.ind("Dep").tag, 1, &args, &v)
                        .expect("the spine is built — it is the kernel that refuses it");
                assert!(
                    e.el.kernel_check_term(
                        &e.el.psi,
                        heather_kernel::layer::Layer::Prog,
                        &cx.gamma,
                        &tm,
                        &ty,
                        &lvl,
                    )
                    .is_err(),
                    "a receiver from a different instantiation must not typecheck"
                );
            }

            #[test]
            fn the_axes_on_a_dependent_telescoped_records_field_reads() {
                // Emission, on real source. A literal receiver (an assembled
                // record value), a neutral one (a parameter and a bare
                // binder), an open element type, and a **checking** position:
                // `d.same` is offered as the proof of a stated equation, so a
                // wrong field type is a rejection and not a different term.
                let mut e = env();
                e.el.enable_emission_walk();
                e.el.elab_source(
                    "
fn mkd<A>(n: Nat, a: A) -> Dep<A>(n) { Dep(n, refl, a) }
fn d_k<A>(n: Nat, d: Dep<A>(n)) -> Nat { d.k }
fn d_a<A>(n: Nat, d: Dep<A>(n)) -> A { d.a }
fn d_same<A>(n: Nat, d: Dep<A>(n)) -> d.k = n { d.same }
fn d_lit() -> Dep<Flat>(2) { Dep(2, refl, FA) }
theorem d_open<A>(n: Nat, a: A): d_k(n, mkd(n, a)) = n { refl }
theorem d_open_a<A>(n: Nat, a: A): d_a(n, mkd(n, a)) = a { refl }
theorem d_literal(): d_k(2, d_lit()) = 2 { refl }
theorem d_literal_a(): d_a(2, d_lit()) = FA { refl }
theorem d_neutral<A>(n: Nat, d: Dep<A>(n)): d_k(n, mkd(n, d_a(n, d))) = n { refl }
theorem d_bare<A>(n: Nat, d: Dep<A>(n)): d.k = n { d.same }
theorem d_bare_lit(): d_lit().k = 2 { d_lit().same }
",
                )
                .expect("a dependent telescoped record's field reads check and compute");
                // Axis 4, three ways.
                assert!(
                    e.el
                        .elab_source("theorem d_false(): d_k(2, d_lit()) = 3 { refl }")
                        .is_err(),
                    "a false equation must be refused"
                );
                assert!(
                    e.el
                        .elab_source(
                            "theorem d_neighbour<A>(n: Nat, d: Dep<A>(n)): d.k = n { d.a }"
                        )
                        .is_err(),
                    "a neighbouring field must not prove this field's statement"
                );
                assert!(
                    e.el
                        .elab_source(
                            "fn d_wrong_field<A>(n: Nat, d: Dep<A>(n)) -> A { d.same }"
                        )
                        .is_err(),
                    "the equality field is not the element field"
                );
                let findings = e.el.take_emission_findings();
                let listed: Vec<String> = findings
                    .iter()
                    .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                    .collect();
                assert!(
                    findings.is_empty(),
                    "the emission walker is empty on dependent telescoped field reads:\n{}",
                    listed.join("\n")
                );
            }

            // -- §2.2 / §2.3: the two hole-matcher extensions ---------------

            /// A value parameter that never occurs bare, a type parameter that
            /// occurs as a **code** in a term slot, and a look-alike of each.
            const HIDDEN: &str = "
fn idn(n: Nat) -> Nat { n }
fn idty<A>(a: A) -> A { a }
record ByApp<A>(n: Nat) { a: A, ok: idn(n) = idn(n) }
record ByAppLk<A>(n: Nat) { a: A, ok: idn(n) = idn(n) }
record ByCode<A> { a: A, ok: idty(a) = a }
record ByCodeLk<A> { a: A, ok: idty(a) = a }
";

            fn env_hidden() -> Env {
                let mut e = env();
                e.el
                    .elab_source(HIDDEN)
                    .expect("the hidden-parameter declarations elaborate");
                e
            }

            #[test]
            fn a_parameter_hidden_under_an_application_is_still_placed() {
                // §2.2: `ByApp`'s `n` occurs only inside `app(idn^δ; n)` — the
                // shape `Certified`'s `begin` (only `begin.offset`) and
                // `Exists`'s `P` (only `P(witness)`) have. Without the `App`
                // arm it is never placed and every use site declines.
                let e = env_hidden();
                let (flat, fl) = e.lowered("Flat");
                let (inline, _) = e
                    .el
                    .lower_instance(
                        &e.cx,
                        &e.ind("ByApp"),
                        &[(flat.clone(), fl.clone())],
                        &[(nat(5), Type::Nat, Level::Zero)],
                        SPAN,
                    )
                    .expect("`ByApp<Flat>(5)` lowers");
                let args =
                    e.el.instance_args(&e.cx, &e.ind("ByApp"), &inline)
                        .expect("the hidden value parameter is recovered");
                assert_eq!(args.len(), 2);
                assert_eq!(*args[1], nat(5), "…as the numeral it is");
                // And the look-alike is a different declaration: the same
                // spine, its own tag, its own name.
                let (lk, _) = e
                    .el
                    .lower_instance(
                        &e.cx,
                        &e.ind("ByAppLk"),
                        &[(flat, fl)],
                        &[(nat(5), Type::Nat, Level::Zero)],
                        SPAN,
                    )
                    .expect("`ByAppLk<Flat>(5)` lowers");
                let r = e.el.respell_ty(&e.cx, &lk).expect("the look-alike respells");
                let Type::El { tm, .. } = &r else { panic!("`El` of an application") };
                assert_eq!(
                    e.el.gen_app_of(tm).map(|(k, _)| k),
                    Some(GenDef::TyCodeFn(e.ind("ByAppLk").tag))
                );
                assert_ne!(
                    r,
                    e.el.respell_ty(&e.cx, &inline).expect("…and so does `ByApp`")
                );
                // The negative the matcher's incompleteness must not swallow:
                // a *different* value argument is a different instantiation.
                let (other, _) = e
                    .el
                    .lower_instance(
                        &e.cx,
                        &e.ind("ByApp"),
                        &[e.lowered("Flat")],
                        &[(nat(6), Type::Nat, Level::Zero)],
                        SPAN,
                    )
                    .expect("`ByApp<Flat>(6)` lowers");
                let other_args =
                    e.el.instance_args(&e.cx, &e.ind("ByApp"), &other)
                        .expect("…and recovers its own");
                assert_ne!(*other_args[1], nat(5));
            }

            #[test]
            fn a_type_parameter_occurring_as_a_code_in_a_term_slot_is_placed() {
                // §2.3: `ByCode`'s `A` is `El (Var i)` in a type slot and the
                // bare `Var i` — its *code* — inside `app(idty^δ; ⌜A⌝, a)`.
                // Recovering a hole as a **code** is what makes the two slots
                // one; recovering the type in one and the code in the other
                // gives `Nat` against `El ⌜Nat⌝`, which disagree
                // syntactically and decline for spelling.
                let e = env_hidden();
                // An **open** element type: both slots carry the parameter's
                // own variable, so the two recoveries are the same code and
                // the placement is the whole content of the test.
                let mut acx = Cx::empty();
                acx.push("#A".into(), Type::Ty(Level::Zero), Level::succ(Level::Zero));
                let a = Type::El {
                    level: Level::Zero,
                    tm: Rc::new(Term::Var(LocalVar(0))),
                };
                let (open, _) = e
                    .el
                    .lower_instance(&acx, &e.ind("ByCode"), &[(a.clone(), Level::Zero)], &[], SPAN)
                    .expect("`ByCode<A>` lowers openly");
                let oargs =
                    e.el.instance_args(&acx, &e.ind("ByCode"), &open)
                        .expect("the type parameter is recovered from both slots at once");
                assert_eq!(oargs.len(), 1);
                assert_eq!(*oargs[0], Term::Var(LocalVar(0)));
                // The look-alike declines to be this one.
                let (lk, _) = e
                    .el
                    .lower_instance(&acx, &e.ind("ByCodeLk"), &[(a, Level::Zero)], &[], SPAN)
                    .expect("`ByCodeLk<A>` lowers openly");
                assert!(
                    e.el.instance_args(&acx, &e.ind("ByCodeLk"), &open).is_none(),
                    "this declaration's lowering is not the look-alike's instantiation"
                );
                assert!(e.el.instance_args(&acx, &e.ind("ByCode"), &lk).is_none());
                // **The boundary the code recovery did not reach**, flipped
                // 2026-09-15 (`docs/closed-argument-and-parameter-domain-
                // spelling-design.md` §3). At a *closed* argument the subject
                // spells the same parameter two ways: a binder's type is a
                // **structural read** and keeps the inline lowering
                // (`docs/annotation-component-respell-design.md` §2.5's own
                // rule), while the type argument of `idty(a)` is an annotation
                // and went through the chokepoint, so it is the reference.
                // `code_of` of the first is `TmSum(…)` and the second is
                // `Flat#tycode^δ`. The recognizer now sees through the name:
                // the two codes agree because their inline copies do, and the
                // **reference** is what is kept — which is what the emitted
                // argument becomes anyway.
                let (flat, fl) = e.lowered("Flat");
                let (closed, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCode"), &[(flat.clone(), fl.clone())], &[], SPAN)
                    .expect("`ByCode<Flat>` lowers");
                let cargs =
                    e.el.instance_args(&e.cx, &e.ind("ByCode"), &closed)
                        .expect("the two spellings of a closed type argument are reconciled");
                assert_eq!(cargs.len(), 1);
                assert!(
                    e.el.is_gen_ref(&cargs[0], GenDef::TyCode(e.ind("Flat").tag)),
                    "…and the recovered argument is the **reference** code"
                );
                // The look-alike does not start matching, which is the one
                // failure mode of the new arm that is not a performance
                // question (§7 item 1): `ByCodeLk<Flat>` is a different
                // declaration with the same lowering shape, and seeing through
                // a name relates no two declarations.
                let (closed_lk, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCodeLk"), &[(flat, fl)], &[], SPAN)
                    .expect("`ByCodeLk<Flat>` lowers");
                assert!(
                    e.el.instance_args(&e.cx, &e.ind("ByCodeLk"), &closed).is_none(),
                    "the look-alike's template is not this declaration's lowering"
                );
                assert!(e.el.instance_args(&e.cx, &e.ind("ByCode"), &closed_lk).is_none());
                // And a genuinely different argument is a different
                // instantiation, recovered as its own reference rather than
                // reconciled with this one.
                let (flat2, f2l) = e.lowered("Flat2");
                let (other, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCode"), &[(flat2, f2l)], &[], SPAN)
                    .expect("`ByCode<Flat2>` lowers");
                let oargs2 =
                    e.el.instance_args(&e.cx, &e.ind("ByCode"), &other)
                        .expect("`ByCode<Flat2>`'s own argument is recovered");
                assert!(
                    e.el.is_gen_ref(&oargs2[0], GenDef::TyCode(e.ind("Flat2").tag)),
                    "a different closed argument recovers a different reference"
                );
                assert_ne!(cargs[0], oargs2[0]);
            }

            #[test]
            fn a_type_argument_arriving_as_a_quote_is_now_seen_through() {
                // **Flipped 2026-09-16** by
                // `docs/instance-match-quote-arm-design.md`. This test was
                // `a_type_argument_arriving_as_a_quote_still_declines`, and it
                // pinned the boundary the *name* arm could not reach: a type
                // argument that arrives as a code literal (`El «Nat»`) against
                // the type it quotes, and the **primitive** `Nat`, which has
                // no name to take at all. Both declined, as
                // `identity-match-El/Nat`.
                //
                // What changed: the matcher's former-mismatch arm now takes
                // **one head step** of `decoded` — the kernel's own
                // `step_type` on an `El` of a canonical code former — where
                // the 2026-09-15 attempt took `decode_deep` and materialized
                // the whole literal at every mismatch node (design §2). The
                // walk that follows is bounded by the **template**, which is a
                // declaration's own lowering, so a multi-megabyte quote is
                // walked only as far as the template is.
                let e = env_hidden();
                // The control is unchanged and still a *name*: a closed
                // argument spelled as a reference is reconciled by the arm
                // above this one, not by the quote arm.
                let (flat, fl) = e.lowered("Flat");
                let (named, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCode"), &[(flat, fl)], &[], SPAN)
                    .expect("`ByCode<Flat>` lowers");
                assert!(
                    e.el.instance_args(&e.cx, &e.ind("ByCode"), &named).is_some(),
                    "a named closed argument is reconciled"
                );
                // The quote, two ways, and both now recover — to the **same**
                // argument, because `El «Nat»` and `Nat` are one type and the
                // recovered hole is a code either way.
                let quoted = Type::El {
                    level: Level::Zero,
                    tm: Rc::new(Term::TmNat),
                };
                let mut recovered = Vec::new();
                for (label, arg) in [("El «Nat»", quoted), ("Nat", Type::Nat)] {
                    let (closed, _) = e
                        .el
                        .lower_instance(&e.cx, &e.ind("ByCode"), &[(arg, Level::Zero)], &[], SPAN)
                        .expect("the instantiation lowers");
                    let args =
                        e.el.instance_args(&e.cx, &e.ind("ByCode"), &closed)
                            .unwrap_or_else(|| panic!("{label}: the quote is seen through"));
                    assert_eq!(args.len(), 1);
                    recovered.push(Rc::clone(&args[0]));
                }
                assert_eq!(
                    recovered[0], recovered[1],
                    "the two spellings of `Nat` recover one code"
                );
                assert_eq!(*recovered[0], Term::TmNat);
                // The negative the arm must not swallow: a quote whose decode
                // is a *different* type still declines. `El ⌜Ty 0⌝` decodes to
                // `Ty 0`, which is not `Nat`, and `ByCodeLk` is still a
                // different declaration.
                let wrong = Type::El {
                    level: Level::succ(Level::Zero),
                    tm: Rc::new(Term::TmTy(Level::Zero)),
                };
                let (wrong_inst, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCode"), &[(wrong, Level::succ(Level::Zero))], &[], SPAN)
                    .map_or_else(|_| (Type::Nat, Level::Zero), |t| t);
                if wrong_inst != Type::Nat {
                    let args = e.el.instance_args(&e.cx, &e.ind("ByCode"), &wrong_inst);
                    assert!(
                        args.is_none_or(|a| *a[0] != Term::TmNat),
                        "a quote of a different type is not `Nat`"
                    );
                }
                let (flat2, f2l) = e.lowered("Flat2");
                let (lk, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCodeLk"), &[(flat2, f2l)], &[], SPAN)
                    .expect("`ByCodeLk<Flat2>` lowers");
                assert!(
                    e.el.instance_args(&e.cx, &e.ind("ByCode"), &lk).is_none(),
                    "the look-alike does not start matching"
                );
            }

            #[test]
            fn the_axes_on_a_record_whose_type_argument_is_a_quote() {
                // The quote arm on real source
                // (`docs/instance-match-quote-arm-design.md` §5 item 8).
                // `ByCode<Nat>`'s `A` argument has no name to take, so before
                // this arm every one of these reads fell to `project_field`'s
                // `Fst`/`Snd` walk. The four axes: a **literal** receiver (an
                // assembled record returned by a `fn` and read through, the
                // idiom the amendment to §7 item 7 of
                // `docs/closed-argument-and-parameter-domain-spelling-design.md`
                // settled on) and a **neutral** one; an **open** element type
                // beside the closed one; a **checking** position, where a
                // wrong field type is a rejection and not a different term;
                // and negative controls below.
                let mut e = env_hidden();
                e.el.enable_emission_walk();
                e.el.elab_source(
                    "
fn mkc<A>(a: A) -> ByCode<A> { ByCode(a, refl) }
fn c_open<A>(c: ByCode<A>) -> A { c.a }
fn c_quoted(c: ByCode<Nat>) -> Nat { c.a }
fn c_named(c: ByCode<Flat>) -> Flat { c.a }
fn c_lit() -> ByCode<Nat> { ByCode(3, refl) }
theorem c_neutral<A>(a: A): c_open(mkc(a)) = a { refl }
theorem c_neutral_q(n: Nat): c_quoted(mkc(n)) = n { refl }
theorem c_literal(): c_quoted(c_lit()) = 3 { refl }
theorem c_bare_lit(): c_lit().a = 3 { refl }
theorem c_checking(c: ByCode<Nat>): idty(c.a) = c.a { c.ok }
theorem c_checking_open<A>(c: ByCode<A>): idty(c.a) = c.a { c.ok }
",
                )
                .expect("a quoted type argument's field reads check and compute");
                // Axis 4: the negatives.
                assert!(
                    e.el
                        .elab_source("theorem c_false(): c_quoted(c_lit()) = 4 { refl }")
                        .is_err(),
                    "a false equation must be refused"
                );
                assert!(
                    e.el
                        .elab_source(
                            "theorem c_neighbour(c: ByCode<Nat>): idty(c.a) = c.a { c.a }"
                        )
                        .is_err(),
                    "a neighbouring field must not prove this field's statement"
                );
                // The emission walker, and what it is allowed to say here.
                // It is **not** empty, and asserting that it were would pin
                // someone else's defect to this test (the 2026-09-15
                // amendment to §7 item 7 of
                // `docs/closed-argument-and-parameter-domain-spelling-design.md`,
                // `issues/emission-walker-residual-sites`): every finding is an
                // `App`'s `dom`/`cod` carrying the boxed `El ⌜Nat⌝` literal,
                // which is the quote layer's standing residue and is exactly
                // the thing `Nat` has no name to replace. So what is asserted
                // is that **`«Nat»` is the only quote in them** — a finding
                // carrying any other boxed code would be this arm's, and is
                // the failure this test exists to catch.
                let findings = e.el.take_emission_findings();
                let listed: Vec<String> = findings
                    .iter()
                    .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                    .collect();
                assert!(
                    findings
                        .iter()
                        .all(|f| !f.found.replace("«Nat»", "").contains('«')),
                    "the only residual quote is the unnameable primitive:\n{}",
                    listed.join("\n")
                );
                // The control, and the reason the assertion above is not
                // vacuous: the same axes at a **named** closed argument leave
                // the walker empty, so the residue is the primitive's and not
                // the device's.
                e.el.elab_source(
                    "
fn n_read(c: ByCode<Flat>) -> Flat { c.a }
fn n_lit() -> ByCode<Flat> { ByCode(FA, refl) }
theorem n_literal(): n_read(n_lit()) = FA { refl }
theorem n_checking(c: ByCode<Flat>): idty(c.a) = c.a { c.ok }
",
                )
                .expect("a named closed argument's field reads check and compute");
                let named_findings = e.el.take_emission_findings();
                let named_listed: Vec<String> = named_findings
                    .iter()
                    .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                    .collect();
                assert!(
                    named_findings.is_empty(),
                    "a named closed argument leaves the emission walker empty:\n{}",
                    named_listed.join("\n")
                );
                // And the route actually changed: a bare-binder read off
                // `ByCode<Nat>` now takes the named projection. `ByCode` is
                // dependent (its `ok` field mentions `a`), so it is exempt
                // from the receiver gate and `instance_args` is the only
                // thing that was declining.
                let quoted = Type::El {
                    level: Level::Zero,
                    tm: Rc::new(Term::TmNat),
                };
                for (label, arg) in [("El «Nat»", quoted), ("Nat", Type::Nat)] {
                    let (inline, il) = e
                        .el
                        .lower_instance(&e.cx, &e.ind("ByCode"), &[(arg, Level::Zero)], &[], SPAN)
                        .expect("the instantiation lowers");
                    let r = e.el.respell_ty(&e.cx, &inline).expect("respells");
                    let mut cx = Cx::empty();
                    cx.push("#v".into(), r.clone(), il.clone());
                    let (tm, ..) = e
                        .el
                        .project_field(
                            &cx,
                            &e.ind("ByCode"),
                            &r.shift_local(1),
                            Rc::new(Term::Var(LocalVar(0))),
                            0,
                            SPAN,
                        )
                        .expect("the read elaborates either way");
                    assert_eq!(
                        e.el.gen_app_of(&tm).map(|(k, _)| k),
                        Some(GenDef::RecProj(e.ind("ByCode").tag, 0)),
                        "{label}: the read takes the named projection"
                    );
                }
            }

            #[test]
            fn a_wrong_instance_closed_projection_is_refused_by_the_kernel() {
                // The control that says the reconciled reference means what it
                // claims. `ByCode<Flat>`'s receiver against the projection at
                // `ByCode<Flat2>`'s recovered arguments: the spine is built —
                // nothing here guards it — and the kernel refuses it.
                let e = env_hidden();
                let (flat, fl) = e.lowered("Flat");
                let (inline, il) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCode"), &[(flat, fl)], &[], SPAN)
                    .expect("`ByCode<Flat>` lowers");
                let r = e.el.respell_ty(&e.cx, &inline).expect("respells");
                let (cx, v) = receiver(&r, &il);
                let (flat2, f2l) = e.lowered("Flat2");
                let (other, _) = e
                    .el
                    .lower_instance(&e.cx, &e.ind("ByCode"), &[(flat2, f2l)], &[], SPAN)
                    .expect("`ByCode<Flat2>` lowers");
                let args =
                    e.el.instance_args(&cx, &e.ind("ByCode"), &other.shift_local(1))
                        .expect("`ByCode<Flat2>`'s arguments are recovered");
                let Some((tm, ty, lvl)) =
                    e.el.rec_proj_ref_at(&cx, e.ind("ByCode").tag, 0, &args, &v)
                else {
                    return;
                };
                assert!(
                    e.el.kernel_check_term(
                        &e.el.psi,
                        heather_kernel::layer::Layer::Prog,
                        &cx.gamma,
                        &tm,
                        &ty,
                        &lvl,
                    )
                    .is_err(),
                    "a receiver from a different instantiation must not typecheck"
                );
            }

            #[test]
            fn the_closed_record_reads_check_and_compute() {
                // The four axes on a record whose registration reaches its use
                // sites only now: a **literal** receiver (an assembled record
                // value), **neutral** ones (a parameter and a bare binder), an
                // **open** element type as the control that the new arm did
                // not change it, and a **checking** position — `r.ok` offered
                // as the proof of a stated equation.
                let mut e = env_hidden();
                e.el.enable_emission_walk();
                e.el.elab_source(
                    "
fn mk_c<A>(a: A) -> ByCode<A> { ByCode(a, refl) }
fn c_a<A>(r: ByCode<A>) -> A { r.a }
fn c_flat(r: ByCode<Flat>) -> Flat { r.a }
fn c_flat_ok(r: ByCode<Flat>) -> idty(r.a) = r.a { r.ok }
fn c_lit() -> ByCode<Flat> { ByCode(FB(1), refl) }
theorem c_open<A>(a: A): c_a(mk_c(a)) = a { refl }
theorem c_closed(): c_flat(c_lit()) = FB(1) { refl }
theorem c_bare_lit(): idty(c_lit().a) = c_lit().a { c_lit().ok }
theorem c_bare(r: ByCode<Flat>): idty(r.a) = r.a { r.ok }
theorem c_neutral(r: ByCode<Flat>): c_flat(mk_c(c_flat(r))) = r.a { refl }
",
                )
                .expect("the closed-argument record's reads check and compute");
                assert!(
                    e.el
                        .elab_source("theorem c_false(): c_flat(c_lit()) = FA { refl }")
                        .is_err(),
                    "a false equation must be refused"
                );
                assert!(
                    e.el
                        .elab_source("fn c_wrong_field(r: ByCode<Flat>) -> Flat { r.ok }")
                        .is_err(),
                    "the equality field is not the element field"
                );
                let findings = e.el.take_emission_findings();
                let listed: Vec<String> = findings
                    .iter()
                    .map(|f| format!("{} {} depth={}: {}", f.decl, f.slot, f.depth, f.found))
                    .collect();
                assert!(
                    findings.is_empty(),
                    "the emission walker is empty on the closed-argument record:\n{}",
                    listed.join("\n")
                );
            }

            #[test]
            fn the_hidden_parameter_records_check_and_compute() {
                // Emission on real source, both records, all four axes.
                let mut e = env_hidden();
                e.el.enable_emission_walk();
                e.el.elab_source(
                    "
fn mk_app<A>(n: Nat, a: A) -> ByApp<A>(n) { ByApp(a, refl) }
fn mk_code<A>(a: A) -> ByCode<A> { ByCode(a, refl) }
fn app_a<A>(n: Nat, r: ByApp<A>(n)) -> A { r.a }
fn code_a<A>(r: ByCode<A>) -> A { r.a }
fn code_ok<A>(r: ByCode<A>) -> idty(r.a) = r.a { r.ok }
theorem app_open<A>(n: Nat, a: A): app_a(n, mk_app(n, a)) = a { refl }
theorem code_open<A>(a: A): code_a(mk_code(a)) = a { refl }
theorem code_literal(): code_a(mk_code(FA)) = FA { refl }
",
                )
                .expect("the hidden-parameter records check and compute");
                assert!(
                    e.el
                        .elab_source("theorem code_false(): code_a(mk_code(FA)) = FB(1) { refl }")
                        .is_err(),
                    "a false equation must be refused"
                );
                let findings = e.el.take_emission_findings();
                assert!(
                    findings.is_empty(),
                    "the emission walker is empty on the hidden-parameter records: {}",
                    findings.len()
                );
            }
        }

        #[test]
        fn the_reflection_boundary_unspells_an_applied_reference() {
            // §4.2's third edit: `fn_type_code` hands a `meta` analyzer the
            // inline instantiation, exactly as it does for a closed code.
            let mut e = env();
            e.el.elab_source("fn bid(b: Box<Flat>) -> Box<Flat> { b }")
                .expect("elaborates");
            let (flat, fl) = e.lowered("Flat");
            let (inline, _) = instance(&e, "Box", &[(flat, fl)]);
            let Some(Term::BoxTy(stmt)) = e.el.fn_type_code("bid") else {
                panic!("the statement reflects as a boxed type")
            };
            let Type::Pi { dom, cod, .. } = &*stmt else {
                panic!("one parameter, one Π")
            };
            assert_eq!(**dom, inline, "the boundary sees the inline instantiation");
            assert_eq!(**cod, inline.shift_local(1));
        }
    }
}
