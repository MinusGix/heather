//! State whose lifetime is one ordinary declaration elaboration.

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, Term, Type};
use heather_syntax::Span;

use crate::context::Cx;
use crate::OperatorFallbackUse;
use crate::goals::{GoalArena, GoalCheckpoint};

/// Scratch state for an ordinary declaration.
///
/// The elaborator itself is a long-lived session. These values are not: they
/// describe one speculative declaration attempt and must be reset together on
/// retry or completion. Keeping them in one object makes that lifetime a
/// structural property instead of a cleanup convention spread across
/// `Elaborator::elab_decl`.
#[derive(Clone, Default)]
pub(super) struct DeclAttempt {
    /// Operator fallbacks taken after consulting a designation table.
    pub(super) op_fallback_notes: RefCell<Vec<String>>,
    /// Successful fallbacks which become lints only if the declaration lands.
    pub(super) op_fallback_uses: RefCell<Vec<OperatorFallbackUse>>,
    /// Checking sites whose inferred type may disagree with the expected one,
    /// in the order they were met. **Candidates, not notes**: nothing is
    /// converted and nothing is spelled here
    /// (`issues/elab-diagnostic-probe-cost.md`). The gate probes them in this
    /// order and stops at the first that has something to say, which is what
    /// reproduces the old eager "first note to fill the slot wins"; on the
    /// common path — the declaration checks — the whole list is dropped
    /// unread.
    pub(super) check_notes: RefCell<Vec<CheckNote>>,
    /// Receivers a dot call placed into a type-owned member that marks no
    /// parameter `self`, by the receiver's span and the member's name. Read
    /// only by the probe of a [`CheckNote`] at that span, to say the receiver
    /// was meant for a later parameter
    /// (issues/type-member-missing-self-diagnostic.md). A mismatch there is
    /// no elaboration error — the kernel is the judge — so the dot call's own
    /// failure path never sees it.
    pub(super) unmarked_receivers: RefCell<Vec<(Span, String)>>,
    /// Every receiver a dot call placed into a member its type selected,
    /// marked `self` or not, by the receiver's span and the member's name.
    /// Read only by the probe of a [`CheckNote`] at that span, to name the
    /// member whose receiver type the value missed — `BitVec::is_nl` at a
    /// `BitVec(16)` (issues/width-specific-method-on-other-width.md).
    pub(super) member_receivers: RefCell<Vec<(Span, String)>>,
    /// Written `refl`s whose two sides are not syntactically equal, in the
    /// order they were met — [`Self::check_notes`]' counterpart, deferred for
    /// its reason and probed the same way. Unlike a checking mismatch this
    /// does not *replace* the gate's report — `NotConvertible` at a named
    /// declaration is what the mutation controls of the certifying pipeline
    /// read — it moves that report to the `refl` and appends the two sides
    /// (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`).
    pub(super) refl_notes: RefCell<Vec<ReflNote>>,
    /// Every `decide` the declaration wrote, with the decision the kernel
    /// will run. Consulted only if the gate says `NotConvertible`: the one
    /// whose decision then re-reduces to the wrong side is the refusal, and
    /// the report names its instance (`docs/tactics/reflection-through-decide-instances-design.md` §4).
    pub(super) decide_uses: RefCell<Vec<DecideUse>>,
    /// Every `trivial` emitted at an expected type its budgeted read did not
    /// reach the head of — a closed verdict left to the gate
    /// (`issues/closed-verdict-evaluated-twice.md`). Consulted, like
    /// [`Self::decide_uses`], only if the gate says `NotConvertible`.
    pub(super) trivial_uses: RefCell<Vec<TrivialUse>>,
    /// Resolved ordinary globals actually inserted while elaborating the
    /// declaration body. Stored by qualified identity, never basename. A
    /// [`DependencySet`] so that a probe or a rejected search candidate can
    /// take its edges back by a length, not by copying the set.
    pub(super) direct_dependencies: RefCell<DependencySet>,

    /// Stable goal identities and their temporary Ψ prefix.
    pub(super) goal_arena: GoalArena,

    /// Constructor-value annotations built once per declaration and shared
    /// by every value of the same type, so repeated values carry the same
    /// allocations and the kernel's conversion memo and pointer-equality
    /// shortcuts answer their repeated queries. Keyed by the type (compared
    /// structurally), the context length, the signature's length and whether
    /// code emits `@`-forms. The length is there because the annotations name
    /// generated definitions, and a declaration registers its own mid-attempt
    /// (`register_gen_defs`): an entry minted before a registration spells
    /// inline what later ones name, and the kernel's shortcut wants one
    /// spelling. Not the goal or `meta fn` padding: a generated definition is
    /// a constant, read the same under any (`Elaborator::gen_def_of`).
    pub(super) children_annotations: RefCell<Vec<(Type, (usize, u32), bool, Rc<Type>, Rc<Type>)>>,
    /// The same for a `sup_f`'s shape and arity slots, keyed by the `Wf`.
    pub(super) wf_slot_annotations: RefCell<Vec<(Type, (usize, u32), (Rc<Type>, Rc<Term>))>>,
    /// `instance_match`'s answers (`gendefs.rs`): the subject type, compared
    /// structurally, under its declaration's tag, the context, the binders
    /// past it, the scratch depth and the signature's length — everything the
    /// match reads (the registry it consults grows only with the signature). A literal names the same instantiations at every constructor
    /// (`At(…, Block([…]))` matches `List<Instruction>` again and again;
    /// `issues/constructor-literal-respell-cost.md`), and each match is a hole
    /// walk, a template instantiated and walked again, and its arguments
    /// emitted.
    pub(super) instance_matches: RefCell<std::collections::HashMap<InstanceMatchKey, Vec<(Type, Option<(Level, Vec<Rc<Term>>)>)>>>,
    /// A character literal checked at `Char` itself, by the character, the
    /// context's base and length, the signature's length and the expected type (compared
    /// structurally): `char::ofNat(code, decide_yes(refl))` read in `char`'s
    /// scope (`literals.rs`) names only globals, so a second `'a'` — every
    /// letter of every string literal — is the first one's term. Each is
    /// otherwise an elaboration and a `Decide` resolution with its kernel
    /// check, and the shared allocation is what the kernel's memo keys on.
    pub(super) char_literals: RefCell<Vec<(char, (Option<u32>, usize, u32), Type, Term)>>,
    /// [`Declarations::emitted_cx`](crate::declarations::Declarations::emitted_cx)'s memo: a binder's type in the
    /// emission spelling, by the stored type's allocation, its position and
    /// the Ψ scope. The stored `Rc` rides along so its address cannot be
    /// reused while the entry stands. Contexts share their spine, so the
    /// tactic calls of one block respell each binder once.
    pub(super) emitted_entries: RefCell<std::collections::HashMap<(usize, usize, usize), (Rc<Type>, Rc<Type>)>>,
    /// [`crate::Elaborator::local`]'s memo: a binder's type weakened past the
    /// binders after it, by the stored type's allocation and how many there
    /// are. The stored `Rc` rides along so its address cannot be reused
    /// while the entry stands. A name is read many times under one scope,
    /// and each reading walked and rebuilt its type; the readings now share
    /// everything below the root, which the kernel's memos key on.
    pub(super) weakened_entries: RefCell<std::collections::HashMap<(usize, u32), (Rc<Type>, Rc<Type>)>>,

    /// Slot retained during an argument-slot ownership probe.
    pub(super) slot_probe_target: Cell<Option<Span>>,
    /// Prevents nested motive-less match speculation.
    pub(super) motive_speculation: Cell<bool>,
    /// Inside a case split's fold of the goal's records to their arguments
    /// (`MotiveSynthesisElab::fold_declarations`): the instance matcher then
    /// reads through constructor values too. Set and restored around the
    /// fold itself, so no mark carries it.
    pub(super) folding_for_motive: Cell<bool>,
    /// Inside the redundant-motive probe (`elab_check_skel_slots`): a written
    /// motive nested under a probed one is not probed again there. Each
    /// probe re-elaborates and kernel-checks its whole match, so probing at
    /// every level doubled the work per level of nesting — `step_mono`'s
    /// three levels cost 8.5x its elaboration (2026-09-17).
    pub(super) motive_redundancy_probe: Cell<bool>,
    /// The pending match equations (docs/language/matching/dependent-match-compiler-design.md
    /// §4.3): the next identity to hand out, and the identities a reader of
    /// hypotheses (`omega`, `linarith`) asked for while their match's arms
    /// elaborated without the equation.
    pub(super) match_eq_next: Cell<u32>,
    pub(super) match_eq_wanted: RefCell<Vec<u32>>,
    /// The declaration's parameter names, in telescope order: the kernel's
    /// outermost binders when it locates a refusal no recorded site
    /// explains, and so the names its note uses for them
    /// (`Elaborator::refused_site_cx`).
    pub(super) telescope: RefCell<crate::spine::Binders>,
    /// The names of the parameters a structurally guarded self-call recursed
    /// on. Cleared by `prepare` but **not** by
    /// `finish`, so the caller of a finished attempt can still read which
    /// parameter its recursion descended on: the meaning check
    /// (issues/recursion-meaning-check.md) splits on it.
    pub(super) recursion_decs: RefCell<Vec<String>>,
}

/// [`DeclAttempt::instance_matches`]' key past the subject type: the tag, the
/// context's base and length, the binders past it, the scratch depth and the
/// signature's length.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct InstanceMatchKey {
    pub(super) tag: u32,
    /// `None` for `·`, else the context variable.
    pub(super) base: Option<u32>,
    pub(super) len: usize,
    pub(super) d: u32,
    pub(super) g: u32,
    pub(super) scope: u32,
    /// [`DeclAttempt::folding_for_motive`] at the time: the two modes read
    /// different shapes and must not share an answer.
    pub(super) for_motive: bool,
}

impl DeclAttempt {
    /// Prepare the same state object for another attempt at the declaration.
    pub(super) fn prepare(&mut self) {
        self.op_fallback_notes.get_mut().clear();
        self.op_fallback_uses.get_mut().clear();
        self.check_notes.get_mut().clear();
        self.unmarked_receivers.get_mut().clear();
        self.member_receivers.get_mut().clear();
        self.refl_notes.get_mut().clear();
        self.decide_uses.get_mut().clear();
        self.trivial_uses.get_mut().clear();
        self.telescope.get_mut().clear();
        self.recursion_decs.get_mut().clear();
        self.direct_dependencies.get_mut().clear();
        self.children_annotations.get_mut().clear();
        self.wf_slot_annotations.get_mut().clear();
        self.instance_matches.get_mut().clear();
        self.char_literals.get_mut().clear();
        self.emitted_entries.get_mut().clear();
        self.weakened_entries.get_mut().clear();
        self.match_eq_wanted.get_mut().clear();
        self.goal_arena.prepare();
    }

    /// Discard goal state produced by a speculative attempt.
    pub(super) fn clear_goals(&mut self) {
        self.goal_arena.clear();
    }

    /// Restore the declaration-independent state after success or failure.
    pub(super) fn finish(&mut self) {
        self.goal_arena.finish();
        self.children_annotations.get_mut().clear();
        self.wf_slot_annotations.get_mut().clear();
        self.instance_matches.get_mut().clear();
        self.char_literals.get_mut().clear();
        self.emitted_entries.get_mut().clear();
        self.weakened_entries.get_mut().clear();
        self.op_fallback_notes.get_mut().clear();
        self.check_notes.get_mut().clear();
        self.unmarked_receivers.get_mut().clear();
        self.member_receivers.get_mut().clear();
        self.refl_notes.get_mut().clear();
        self.decide_uses.get_mut().clear();
        self.trivial_uses.get_mut().clear();
        self.telescope.get_mut().clear();
    }

    /// Where a speculative probe started ([`crate::Elaborator::probe`]): the
    /// length of every log, and the value of every cell. O(fields), whatever
    /// the attempt has recorded — the probe's clone used to copy all of it,
    /// a fifth of cold elaboration on operator-heavy files
    /// (`issues/elab-probe-clone-copies-attempt.md`).
    ///
    /// Names every field, so a new one has to pick its probe rule.
    pub(super) fn mark(&self) -> AttemptMark {
        let DeclAttempt {
            op_fallback_notes,
            op_fallback_uses,
            check_notes,
            unmarked_receivers,
            member_receivers,
            refl_notes,
            decide_uses,
            trivial_uses,
            direct_dependencies,
            goal_arena,
            children_annotations,
            wf_slot_annotations,
            // Hash maps, so they have no length to cut back to. Kept across a
            // probe unless it allocated a goal (`Self::restore`).
            instance_matches: _,
            emitted_entries: _,
            // A function of the node and the distance alone: kept.
            weakened_entries: _,
            char_literals,
            slot_probe_target,
            motive_speculation,
            folding_for_motive: _,
            motive_redundancy_probe,
            match_eq_next,
            match_eq_wanted,
            telescope,
            recursion_decs,
        } = self;
        AttemptMark {
            op_fallback_notes: op_fallback_notes.borrow().len(),
            op_fallback_uses: op_fallback_uses.borrow().len(),
            check_notes: check_notes.borrow().len(),
            unmarked_receivers: unmarked_receivers.borrow().len(),
            member_receivers: member_receivers.borrow().len(),
            refl_notes: refl_notes.borrow().len(),
            decide_uses: decide_uses.borrow().len(),
            trivial_uses: trivial_uses.borrow().len(),
            direct_dependencies: direct_dependencies.borrow().mark(),
            goal_arena: goal_arena.checkpoint(),
            children_annotations: children_annotations.borrow().len(),
            wf_slot_annotations: wf_slot_annotations.borrow().len(),
            char_literals: char_literals.borrow().len(),
            slot_probe_target: slot_probe_target.get(),
            motive_speculation: motive_speculation.get(),
            motive_redundancy_probe: motive_redundancy_probe.get(),
            match_eq_next: match_eq_next.get(),
            match_eq_wanted: match_eq_wanted.borrow().len(),
            telescope: telescope.borrow().clone(),
            recursion_decs: recursion_decs.borrow().len(),
        }
    }

    /// Take the attempt back to `mark`: every log cut to its length, every
    /// cell given its value back, the goal arena restored
    /// ([`GoalArena::restore`]).
    ///
    /// Every log here only grows between `prepare` and `finish` — the ones
    /// that are cleared or drained are so on `&mut` paths a probe (which
    /// holds `&self`) cannot reach — so the cut is exact. The vector memos
    /// are cut too; their entries are keyed by the Ψ scope and context, and
    /// cutting them costs only a recomputation. The two hash-map memos keep
    /// a probe's entries, unless the probe allocated a goal: a key may
    /// mention a slot, and the slot it named is about to be freed for another
    /// goal, so they are dropped then.
    pub(super) fn restore(&self, mark: AttemptMark) {
        let DeclAttempt {
            op_fallback_notes,
            op_fallback_uses,
            check_notes,
            unmarked_receivers,
            member_receivers,
            refl_notes,
            decide_uses,
            trivial_uses,
            direct_dependencies,
            goal_arena,
            children_annotations,
            wf_slot_annotations,
            instance_matches,
            emitted_entries,
            // A weakening is a function of the node and the distance, and
            // names no slot: a probe's entries stand whatever it allocated.
            weakened_entries: _,
            char_literals,
            slot_probe_target,
            motive_speculation,
            folding_for_motive: _,
            motive_redundancy_probe,
            match_eq_next,
            match_eq_wanted,
            telescope,
            recursion_decs,
        } = self;
        op_fallback_notes.borrow_mut().truncate(mark.op_fallback_notes);
        op_fallback_uses.borrow_mut().truncate(mark.op_fallback_uses);
        check_notes.borrow_mut().truncate(mark.check_notes);
        unmarked_receivers.borrow_mut().truncate(mark.unmarked_receivers);
        member_receivers.borrow_mut().truncate(mark.member_receivers);
        refl_notes.borrow_mut().truncate(mark.refl_notes);
        decide_uses.borrow_mut().truncate(mark.decide_uses);
        trivial_uses.borrow_mut().truncate(mark.trivial_uses);
        direct_dependencies.borrow_mut().rollback(mark.direct_dependencies);
        if goal_arena.restore(mark.goal_arena) {
            instance_matches.borrow_mut().clear();
            emitted_entries.borrow_mut().clear();
        }
        children_annotations.borrow_mut().truncate(mark.children_annotations);
        wf_slot_annotations.borrow_mut().truncate(mark.wf_slot_annotations);
        char_literals.borrow_mut().truncate(mark.char_literals);
        slot_probe_target.set(mark.slot_probe_target);
        motive_speculation.set(mark.motive_speculation);
        motive_redundancy_probe.set(mark.motive_redundancy_probe);
        // As the clone probe did before #372: a probe's match equations,
        // handed out or asked for, go with it.
        match_eq_next.set(mark.match_eq_next);
        match_eq_wanted.borrow_mut().truncate(mark.match_eq_wanted);
        *telescope.borrow_mut() = mark.telescope;
        recursion_decs.borrow_mut().truncate(mark.recursion_decs);
    }
}

/// [`DeclAttempt::mark`]'s answer.
pub(super) struct AttemptMark {
    op_fallback_notes: usize,
    op_fallback_uses: usize,
    check_notes: usize,
    unmarked_receivers: usize,
    member_receivers: usize,
    refl_notes: usize,
    decide_uses: usize,
    trivial_uses: usize,
    direct_dependencies: usize,
    goal_arena: GoalCheckpoint,
    children_annotations: usize,
    wf_slot_annotations: usize,
    char_literals: usize,
    slot_probe_target: Option<Span>,
    motive_speculation: bool,
    motive_redundancy_probe: bool,
    match_eq_next: u32,
    match_eq_wanted: usize,
    telescope: crate::spine::Binders,
    recursion_decs: usize,
}

/// [`DeclAttempt::direct_dependencies`]: a set of qualified names that
/// remembers the order its members arrived in, so that a rollback is a
/// length ([`Self::mark`], [`Self::rollback`]) and not a copy of the set.
/// Probes and rejected search candidates take their edges back this way, and
/// a search tries one candidate after another.
#[derive(Clone, Default)]
pub(super) struct DependencySet {
    names: BTreeSet<String>,
    /// The members in the order they were first inserted.
    arrived: Vec<String>,
}

impl DependencySet {
    pub(super) fn insert(&mut self, name: String) {
        if !self.names.contains(&name) {
            self.names.insert(name.clone());
            self.arrived.push(name);
        }
    }

    pub(super) fn clear(&mut self) {
        self.names.clear();
        self.arrived.clear();
    }

    /// The members in name order.
    pub(super) fn iter(&self) -> impl Iterator<Item = &String> {
        self.names.iter()
    }

    pub(super) fn mark(&self) -> usize {
        self.arrived.len()
    }

    /// Forget every member that arrived after `mark`.
    pub(super) fn rollback(&mut self, mark: usize) {
        for name in self.arrived.drain(mark.min(self.arrived.len())..) {
            self.names.remove(&name);
        }
    }
}

/// One written `decide`: the `or_index(inst.dec)` its `refl` claims is `0`,
/// the context it was checked in, and what to call the goal and the instance.
#[derive(Clone)]
pub(super) struct DecideUse {
    pub(super) span: Span,
    pub(super) gamma: LocalCtx,
    pub(super) index: Term,
    pub(super) goal: String,
    pub(super) instance: String,
}

/// A `trivial` whose expected type was left unread
/// ([`DeclAttempt::trivial_uses`]): the expected type in its context, so the
/// failure path can reduce it under the gate's budget and say what it is.
#[derive(Clone)]
pub(super) struct TrivialUse {
    pub(super) span: Span,
    pub(super) cx: Rc<Cx>,
    pub(super) expected: Type,
}

/// One checking site met in checking-falls-back-to-inference position: what
/// was inferred, what was expected, and where.
///
/// Everything the probe needs to reproduce its message exactly, and nothing
/// more. The context is cloned because the spelling reads its names, aliases
/// and type variables; the two types are `Rc`-shared kernel nodes, so what is
/// really held alive is one declaration attempt's worth of terms that the
/// attempt is holding anyway.
///
/// The context sits behind an `Rc` because speculative probes clone the
/// whole elaborator, and with it every note recorded so far: a `Cx` by value
/// re-allocated each note's binder names per probe, about a fifth of cold
/// elaboration on operator-heavy files
/// (issues/elab-probe-clone-copies-attempt.md).
#[derive(Clone)]
pub(super) struct CheckNote {
    pub(super) span: Span,
    pub(super) cx: Rc<Cx>,
    pub(super) got: Type,
    pub(super) expected: Type,
    pub(super) level: Level,
    /// An implicit the argument's type disagreed about, for the message.
    pub(super) clash: Option<crate::application::SlotClash>,
    /// The head of the checked call, as written, read for the message only
    /// if it names a `partial fn` (docs/language/partial-functions-design.md §4.2).
    pub(super) partial: Option<String>,
}

/// One written `refl` and the equation it claimed, for the same deferred
/// probe ([`CheckNote`]).
#[derive(Clone)]
pub(super) struct ReflNote {
    pub(super) span: Span,
    pub(super) cx: Rc<Cx>,
    pub(super) lhs: Term,
    pub(super) rhs: Term,
    pub(super) ty: Type,
    pub(super) level: Level,
}

#[cfg(test)]
mod tests {
    use super::DependencySet;

    #[test]
    fn dependency_set_rolls_back_by_arrival() {
        let mut set = DependencySet::default();
        set.insert("b".into());
        let mark = set.mark();
        set.insert("a".into());
        set.insert("b".into());
        set.insert("c".into());
        assert_eq!(set.iter().cloned().collect::<Vec<_>>(), ["a", "b", "c"]);
        set.rollback(mark);
        assert_eq!(set.iter().cloned().collect::<Vec<_>>(), ["b"], "an existing member is not forgotten");
    }
}
