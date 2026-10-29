//! State whose lifetime is one ordinary declaration elaboration.

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, Term, Type};
use heather_syntax::Span;

use crate::context::Cx;
use crate::{OperatorFallbackUse, goals::GoalArena};

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
    /// the report names its instance (`docs/reflection-through-decide-instances-design.md` §4).
    pub(super) decide_uses: RefCell<Vec<DecideUse>>,
    /// Resolved ordinary globals actually inserted while elaborating the
    /// declaration body. Stored by qualified identity, never basename.
    pub(super) direct_dependencies: RefCell<BTreeSet<String>>,

    /// Stable goal identities and their temporary Ψ prefix.
    pub(super) goal_arena: GoalArena,

    /// Constructor-value annotations built once per declaration and shared
    /// by every value of the same type, so repeated values carry the same
    /// allocations and the kernel's conversion memo and pointer-equality
    /// shortcuts answer their repeated queries. Keyed by the type (compared
    /// structurally), the context length, the Ψ scope and whether code emits
    /// `@`-forms. The scope is there because the annotations name generated
    /// definitions, and a declaration registers its own mid-attempt
    /// (`register_gen_defs`): an entry minted before a push names every
    /// global one too close (`docs/iwf-named-signature-design.md` §2).
    pub(super) children_annotations: RefCell<Vec<(Type, (usize, u32), bool, Rc<Type>, Rc<Type>)>>,
    /// The same for a `sup_f`'s shape and arity slots, keyed by the `Wf`.
    pub(super) wf_slot_annotations: RefCell<Vec<(Type, (usize, u32), (Rc<Type>, Rc<Term>))>>,
    /// `instance_match`'s answers (`gendefs.rs`): the subject type, compared
    /// structurally, under its declaration's tag, the context, the binders
    /// past it, the scratch depth and the Ψ scope — everything the match
    /// reads. A literal names the same instantiations at every constructor
    /// (`At(…, Block([…]))` matches `List<Instruction>` again and again;
    /// `issues/constructor-literal-respell-cost.md`), and each match is a hole
    /// walk, a template instantiated and walked again, and its arguments
    /// emitted.
    pub(super) instance_matches: RefCell<std::collections::HashMap<InstanceMatchKey, Vec<(Type, Option<(Level, Vec<Rc<Term>>)>)>>>,
    /// A character literal checked at `Char` itself, by the character, the
    /// context's base and length, the Ψ scope and the expected type (compared
    /// structurally): `char::ofNat(code, decide_yes(refl))` read in `char`'s
    /// scope (`literals.rs`) names only globals, so a second `'a'` — every
    /// letter of every string literal — is the first one's term. Each is
    /// otherwise an elaboration and a `Decide` resolution with its kernel
    /// check, and the shared allocation is what the kernel's memo keys on.
    pub(super) char_literals: RefCell<Vec<(char, (Option<u32>, usize, u32), Type, Term)>>,
    /// [`crate::Elaborator::emitted_cx`]'s memo: a binder's type in the
    /// emission spelling, by the stored type's allocation, its position and
    /// the Ψ scope. The stored `Rc` rides along so its address cannot be
    /// reused while the entry stands. Contexts share their spine, so the
    /// tactic calls of one block respell each binder once.
    pub(super) emitted_entries: RefCell<std::collections::HashMap<(usize, usize, usize), (Rc<Type>, Rc<Type>)>>,

    /// Slot retained during an argument-slot ownership probe.
    pub(super) slot_probe_target: Cell<Option<Span>>,
    /// Prevents nested motive-less match speculation.
    pub(super) motive_speculation: Cell<bool>,
    /// Inside the redundant-motive probe (`elab_check_skel_slots`): a written
    /// motive nested under a probed one is not probed again there. Each
    /// probe re-elaborates and kernel-checks its whole match, so probing at
    /// every level doubled the work per level of nesting — `step_mono`'s
    /// three levels cost 8.5x its elaboration (2026-09-17).
    pub(super) motive_redundancy_probe: Cell<bool>,
    /// The declaration's parameter names, in telescope order: the kernel's
    /// outermost binders when it locates a refusal no recorded site
    /// explains, and so the names its note uses for them
    /// (`Elaborator::refused_site_cx`).
    pub(super) telescope: RefCell<Vec<String>>,
}

/// [`DeclAttempt::instance_matches`]' key past the subject type: the tag, the
/// context's base and length, the binders past it, the scratch depth and the
/// Ψ scope (`Elaborator::lowering_scope`).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct InstanceMatchKey {
    pub(super) tag: u32,
    /// `None` for `·`, else the context variable.
    pub(super) base: Option<u32>,
    pub(super) len: usize,
    pub(super) d: u32,
    pub(super) g: u32,
    pub(super) scope: u32,
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
        self.telescope.get_mut().clear();
        self.direct_dependencies.get_mut().clear();
        self.children_annotations.get_mut().clear();
        self.wf_slot_annotations.get_mut().clear();
        self.instance_matches.get_mut().clear();
        self.char_literals.get_mut().clear();
        self.emitted_entries.get_mut().clear();
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
        self.op_fallback_notes.get_mut().clear();
        self.check_notes.get_mut().clear();
        self.unmarked_receivers.get_mut().clear();
        self.member_receivers.get_mut().clear();
        self.refl_notes.get_mut().clear();
        self.decide_uses.get_mut().clear();
        self.telescope.get_mut().clear();
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

/// One checking site met in checking-falls-back-to-inference position: what
/// was inferred, what was expected, and where.
///
/// Everything the probe needs to reproduce its message exactly, and nothing
/// more. The context is cloned because the spelling reads its names, aliases
/// and type variables; the two types are `Rc`-shared kernel nodes, so what is
/// really held alive is one declaration attempt's worth of terms that the
/// attempt is holding anyway.
#[derive(Clone)]
pub(super) struct CheckNote {
    pub(super) span: Span,
    pub(super) cx: Cx,
    pub(super) got: Type,
    pub(super) expected: Type,
    pub(super) level: Level,
}

/// One written `refl` and the equation it claimed, for the same deferred
/// probe ([`CheckNote`]).
#[derive(Clone)]
pub(super) struct ReflNote {
    pub(super) span: Span,
    pub(super) cx: Cx,
    pub(super) lhs: Term,
    pub(super) rhs: Term,
    pub(super) ty: Type,
    pub(super) level: Level,
}
