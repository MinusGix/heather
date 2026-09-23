//! Classifying a width fold as a **bit transducer**, and running it over a
//! word (`docs/native-bitvector-values-design.md` §§4, 5, 6).
//!
//! There is no eliminator for `Vec`. Every bitvector operation in the
//! library is `elim_Nat` **on the width**, whose motive at `Succ k` is a
//! function type over vectors and whose step conses one bit and recurses. So
//! the thing to classify is not a `Nat` algebra — `probe.rs` already decides
//! those, and reports `Opaque` here because the step returns a function —
//! but a Mealy machine over the bit alphabet:
//!
//! ```text
//! step k ih  x⃗ s  ⇝  cons( out(b⃗, s) , ih( tail(x⃗) , next(b⃗, s) ) )
//! ```
//!
//! with `out` and `next` **closed**. The class is decided by *evaluating*
//! the step at every closed combination of head bits and state — a truth
//! table, not an induction — and the tails are handled by the same
//! substitution property the `Nat` classes rest on: the probe's tails are
//! neutral variables, so a value that comes back with no stuck case split on
//! them was reached by a reduction that holds at every instantiation of
//! them.
//!
//! Nothing here reads a definition's spelling. The argument modes come from
//! the eliminator's own **motive**, which is an annotation the calculus
//! supplies; the output mode comes from the shape of the value the probe
//! computed. What does not classify — an open `Fin` index, a recursion on a
//! shift count, a state type above the cap — folds exactly as it does today.
//!
//! ### The wrapper (a correction to §4.2; design §13)
//!
//! §4.2 says each domain "whnfs to a `Vec` at a successor length". It does
//! not: the library's vectors arrive inside a *record*, and a record is a
//! one-constructor tier-0 inductive — a Σ-nest whose other components are
//! proof-irrelevant tags (`docs/inductive-tier0-lowering.md` §3). So a
//! peeled argument's type is a `Vec` **in a unit-like Σ-context**, and this
//! module works with the projection path to it ([`Slot`]) rather than with
//! the vector alone. That is still an annotation of the eliminator and not a
//! definition's shape: the path is found by walking the *type*, and every
//! component it does not pass through must be the canonical inhabitant of a
//! unit-like type — exactly the criterion `bits.rs` already decides for a
//! bit's payload, and for the same reason (it is proof-irrelevant, so
//! rebuilding it reproduces the value rather than a merely convertible one).

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::term::Type;
use crate::value::algebra::{add_increments, AffineTree, FoldClass, Increment, Proj};
use crate::value::program::ContextProgram;
use crate::value::transducer::{scale, ArgMode, EnumVal, Output, Transducer, TABLE_CAP};
use crate::value::{
    BitTy, Elim, Env, Head, PiAnn, SigAnn, SumAnn, TmClo, TyClo, VTy, Val, BIT_RUN_WIDTH_CAP,
};

use super::bits::UNIT_NEST_LIMIT;
use super::{Eval, Res, Work};

/// The reserved probe levels this module adds to `probe.rs`'s three. Γ is
/// never this deep, and the gaps keep a misread impossible.
const PROBE_IH: u32 = u32::MAX - 8;
const PROBE_K: u32 = u32::MAX - 16;
const PROBE_TAIL: u32 = u32::MAX - 64;
const PROBE_CARRIED: u32 = u32::MAX - 128;

/// How deep a record wrapper, or an enumerable type's nest, may be. Both are
/// `O(log id_D)` in practice; the bound exists so that neither walk can
/// recurse on the native stack over an adversarial type.
const NEST_LIMIT: u32 = 24;

/// How many `(combination, recursive value)` pairs a finite-output probe may
/// evaluate. The table is capped at [`TABLE_CAP`]; this bounds the product,
/// since a finite output probes the step once per enumerated value of its
/// own type as well as once per combination.
const FINITE_PROBE_CAP: usize = 64;

/// The projection path from an argument (or a result) to the `Vec` inside
/// it — empty when the type *is* a vector. See the module doc.
type Slot = Vec<Proj>;

/// A `Vec` found inside a type: where it sits, and what it is.
struct VecAt<'v> {
    slot: Slot,
    /// The type the slot is a path *into*: what a rebuilt wrapper is built
    /// at, and what its Σ annotations come from.
    outer: &'v TyClo<'v>,
    level: Level,
    elem: &'v TyClo<'v>,
    /// The vector's length, unforced.
    len: &'v TmClo<'v>,
}

/// What one walk of the motive's Π-chain found.
struct Walk<'v> {
    modes: Vec<ArgMode>,
    /// Per peeled argument: where its vector sits inside its type.
    peeled: Vec<Slot>,
    /// Per state argument, its enumeration.
    state_enums: Vec<Vec<EnumVal>>,
    args: Vec<&'v TmClo<'v>>,
    /// The codomain, after every argument has been applied.
    cod: &'v TyClo<'v>,
}

enum Mode<'v> {
    Peeled(VecAt<'v>),
    State(Vec<EnumVal>),
    Carried,
}

impl<'a, 'v> Eval<'a, 'v> {
    // -----------------------------------------------------------------
    // The class
    // -----------------------------------------------------------------

    /// The transducer class of `step` under `motive`, probed once per
    /// `(step, motive)` pair and memoized in the arena.
    ///
    /// The memo is keyed on **both** closures, not on the step alone as the
    /// `Nat` classes are: the argument modes are read off the motive, so two
    /// eliminations sharing a step but not a motive are two different
    /// questions. The negative verdict is memoized too — it is the common
    /// one, and it is what keeps the probe off every ordinary `Nat` fold
    /// after the first.
    pub(super) fn classify_transducer(
        &mut self,
        step: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
    ) -> Res<Option<Rc<Transducer>>> {
        if let Some(found) = self.arena.transducer(step, motive) {
            return Ok(found);
        }
        let decided = self.probe_transducer(step, motive)?.map(Rc::new);
        self.arena.cache_transducer(step, motive, decided.clone());
        Ok(decided)
    }

    fn transduce_var(&self, level: u32) -> &'v TmClo<'v> {
        self.vclo(Rc::new(Val::var(level)))
    }

    fn probe_transducer(
        &mut self,
        step: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
    ) -> Res<Option<Transducer>> {
        let k = self.transduce_var(PROBE_K);
        let succ_k = self.vclo(Rc::new(Val::Succ(k)));
        // One walk with a representative choice says how many combinations
        // there are; the table's walks repeat it at each of them.
        let Some(shape) = self.walk_motive(motive, succ_k, 0, &[])? else {
            return Ok(None);
        };
        let peeled = shape.peeled.len() as u32;
        // A fold with no vector anywhere in sight is an ordinary `Nat` fold
        // that `probe.rs` already declined; do not evaluate its step again.
        // The class needs either a bit to read or a word to produce, and
        // this gate is what keeps the probe off every fold in the library
        // that is not a bitvector operation.
        let out_at = self.vec_in(shape.cod, NEST_LIMIT)?;
        if peeled == 0 && out_at.is_none() {
            return Ok(None);
        }
        let states: usize =
            shape.state_enums.iter().map(Vec::len).product::<usize>().max(1);
        if peeled > 4 || (states << peeled) > TABLE_CAP as usize {
            return Ok(None);
        }
        let combos = combinations(&shape.state_enums, peeled, states);
        // **Pass** is decided before the result type is consulted: a step
        // that hands the recursive result back untouched is one whatever
        // that result is — `carry_bits` folds a carry over two vectors and
        // returns a `Bool` it never inspects — so asking "is the codomain a
        // vector?" first would refuse the whole carry family (design §13).
        if let Some(class) =
            self.probe_word_output(step, motive, succ_k, &shape, &combos, out_at)?
        {
            return Ok(Some(class));
        }
        self.probe_value_output(step, motive, succ_k, &shape, &combos)
    }

    /// The **cons** and **pass** outputs: the step either puts one bit on
    /// the recursive result or hands it back, the head bits and the state
    /// driving both. `None` means neither, and the caller asks the value
    /// outputs next.
    fn probe_word_output(
        &mut self,
        step: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
        succ_k: &'v TmClo<'v>,
        shape: &Walk<'v>,
        combos: &[(u32, Vec<usize>)],
        out_at: Option<VecAt<'v>>,
    ) -> Res<Option<Transducer>> {
        let mut bits = Vec::with_capacity(combos.len());
        let mut next = Vec::with_capacity(combos.len());
        let mut passing: Option<bool> = None;
        for (combo, choice) in combos {
            let Some(walk) = self.walk_motive(motive, succ_k, *combo, choice)? else {
                return Ok(None);
            };
            if walk.modes != shape.modes {
                return Ok(None);
            }
            let value = self.transduce_apply(step, &walk.args)?;
            // **Pass**: the value *is* the recursive call, at the arguments
            // the class says.
            if let Some(state) = self.recursive_call(&value, shape, &[])? {
                if *passing.get_or_insert(true) {
                    next.push(state);
                    continue;
                }
                return Ok(None);
            }
            if passing == Some(true) {
                return Ok(None);
            }
            let Some(at) = &out_at else { return Ok(None) };
            passing = Some(false);
            // **Cons**: the vector inside the value is `⟨bit, ih(…).slot⟩`.
            let slot = at.slot.clone();
            let Some(inner) = self.slot_of(&slot, value)? else { return Ok(None) };
            let Val::Pair { fst, snd, .. } = &*inner else { return Ok(None) };
            let head = self.force(fst)?;
            let head = self.delta_whnf(head)?;
            let Some(bit) = self.bit_of(&head)? else { return Ok(None) };
            let rest = self.force(snd)?;
            let rest = self.delta_whnf(rest)?;
            let Some(state) = self.recursive_call(&rest, shape, &slot)? else {
                return Ok(None);
            };
            bits.push(bit);
            next.push(state);
        }
        let (out_slot, output) = match (passing.unwrap_or(true), &out_at) {
            (true, _) => (Vec::new(), Output::Pass),
            (false, Some(at)) => (at.slot.clone(), Output::Cons { bits }),
            (false, None) => return Ok(None),
        };
        Ok(Some(Transducer {
            modes: shape.modes.clone(),
            peeled: shape.peeled.len() as u32,
            slots: shape.peeled.clone(),
            out_slot,
            states: state_values(&shape.state_enums),
            state_enums: shape.state_enums.clone(),
            next,
            output,
        }))
    }

    /// The **finite** and **scaled** outputs (design §5): the fold's result
    /// is not a vector but a value of a finitely enumerable type, or a
    /// `Nat`.
    ///
    /// Neither may have a state argument. A finite output is read by
    /// replaying, on each enumerated value of *its own* type, the
    /// eliminations the step performs on its recursive call — the step's
    /// own case split on the result is what the table records — and that
    /// replay never applies the step again, so it cannot observe where the
    /// arguments went. A state whose transition is invisible cannot be
    /// tabulated, so a step with one is declined rather than guessed at.
    fn probe_value_output(
        &mut self,
        step: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
        succ_k: &'v TmClo<'v>,
        shape: &Walk<'v>,
        combos: &[(u32, Vec<usize>)],
    ) -> Res<Option<Transducer>> {
        if !shape.state_enums.is_empty() {
            return Ok(None);
        }
        let out_ty = shape.cod;
        let w = self.force_ty(out_ty)?;
        let w = self.delta_whnf_ty(w)?;
        if matches!(&*w, VTy::Nat) {
            return self.probe_scaled(step, motive, succ_k, shape, combos);
        }
        let Some(values) = self.enumerate(out_ty, NEST_LIMIT)? else { return Ok(None) };
        if combos.len() * values.len() > FINITE_PROBE_CAP {
            return Ok(None);
        }
        let mut table = vec![0u32; combos.len() * values.len()];
        for (i, (combo, choice)) in combos.iter().enumerate() {
            let Some(walk) = self.walk_motive(motive, succ_k, *combo, choice)? else {
                return Ok(None);
            };
            if walk.modes != shape.modes {
                return Ok(None);
            }
            // Routing first, with a neutral `ih`: either the recursive call
            // is not used at all at this combination — the fold
            // short-circuits, and there is nothing to route — or it is used
            // at the arguments the class says, and the value is that call
            // followed by the eliminations the step performs on its result.
            let probed = self.transduce_apply(step, &walk.args)?;
            let uses_ih = matches!(&*probed,
                Val::Neutral(n) if matches!(n.head, Head::Var(PROBE_IH)));
            let past_call = if uses_ih {
                let Some(rest) = self.call_arguments(&probed, shape)? else {
                    return Ok(None);
                };
                rest
            } else {
                Vec::new()
            };
            for (j, value) in values.iter().enumerate() {
                let out = if uses_ih {
                    // The table's row at this recursive value is those same
                    // eliminations **replayed on the closed value**, with
                    // `ih` still neutral. Substituting a constant function
                    // for `ih` instead would also answer a *second* call the
                    // step might make inside a branch — `case(ih(tails))
                    // { … => ih(other) }` — with the value of the first,
                    // and tabulate a fold that is not a function of
                    // `ih(tails)` at all. Replayed, such a branch is a stuck
                    // neutral on `ih`, does not read back, and declines.
                    let Some(v) = self.enum_value(out_ty, value)? else { return Ok(None) };
                    let mut cur = self.force(v)?;
                    for elim in &past_call {
                        cur = self.elim(cur, (*elim).clone())?;
                    }
                    let cur = self.delta_whnf(cur)?;
                    self.read_enum(&cur, NEST_LIMIT)?
                } else {
                    self.read_enum(&probed, NEST_LIMIT)?
                };
                let Some(index) = out.and_then(|o| values.iter().position(|v| *v == o)) else {
                    return Ok(None);
                };
                table[i * values.len() + j] = index as u32;
            }
        }
        Ok(Some(Transducer {
            modes: shape.modes.clone(),
            peeled: shape.peeled.len() as u32,
            slots: shape.peeled.clone(),
            out_slot: Vec::new(),
            states: vec![EnumVal::Triv],
            state_enums: Vec::new(),
            next: vec![0; combos.len()],
            output: Output::Finite { values, table },
        }))
    }

    /// `ih ↦ q·ih + r` at each combination (design §5): the probe value is
    /// `Succ^m` over a neutral whose head is `ih` and whose spine is the
    /// recursive call followed by `Nat` folds that are themselves
    /// **classified** — uniformly affine with a successor-only tree, which
    /// is the shape whose value at `x` is `q·x + base`. Reading it means
    /// calling `classify_step` on the *inner* folds, which is the whole of
    /// what §5 asked for.
    fn probe_scaled(
        &mut self,
        step: &'v TmClo<'v>,
        motive: &'v TyClo<'v>,
        succ_k: &'v TmClo<'v>,
        shape: &Walk<'v>,
        combos: &[(u32, Vec<usize>)],
    ) -> Res<Option<Transducer>> {
        let mut maps = Vec::with_capacity(combos.len());
        for (combo, choice) in combos {
            let Some(walk) = self.walk_motive(motive, succ_k, *combo, choice)? else {
                return Ok(None);
            };
            if walk.modes != shape.modes {
                return Ok(None);
            }
            let value = self.transduce_apply(step, &walk.args)?;
            let (outer, tail) = self.strip_run(value)?;
            let Val::Neutral(n) = &*tail else { return Ok(None) };
            if !matches!(n.head, Head::Var(PROBE_IH)) {
                return Ok(None);
            }
            let Some(rest) = self.call_arguments(&tail, shape)? else { return Ok(None) };
            // `(q, r)`, innermost fold first.
            let mut acc: (Increment, Increment) = (Some(ContextProgram::run((), ONE)), None);
            for elim in rest {
                let Elim::ElimNat { base, step: inner, .. } = elim else { return Ok(None) };
                let class = self.classify_step(inner)?;
                let FoldClass::Affine { tree: AffineTree::Leaf { inc, path }, uniform: true } =
                    &*class
                else {
                    return Ok(None);
                };
                if !path.is_empty() {
                    return Ok(None);
                }
                let q = inc.clone();
                let b = self.force(base)?;
                let b = self.delta_whnf(b)?;
                let (r, zero) = self.strip_run(b)?;
                if !matches!(&*zero, Val::Zero) {
                    return Ok(None);
                }
                let (qa, ra) = acc;
                acc = (scale(&q, &qa), add_increments(&scale(&q, &ra), &r));
            }
            let (q, r) = acc;
            maps.push((q, add_increments(&r, &outer)));
        }
        Ok(Some(Transducer {
            modes: shape.modes.clone(),
            peeled: shape.peeled.len() as u32,
            slots: shape.peeled.clone(),
            out_slot: Vec::new(),
            states: vec![EnumVal::Triv],
            state_enums: Vec::new(),
            next: vec![0; combos.len()],
            output: Output::Scaled { maps },
        }))
    }

    // -----------------------------------------------------------------
    // Reading a probe value
    // -----------------------------------------------------------------

    /// `v` is exactly `ih(args)` — at the arguments the class says —
    /// followed by the projections of `slot` and nothing else. The answer is
    /// the state index the step moved to.
    fn recursive_call(
        &mut self,
        v: &Rc<Val<'v>>,
        shape: &Walk<'v>,
        slot: &[Proj],
    ) -> Res<Option<u32>> {
        let Val::Neutral(n) = &**v else { return Ok(None) };
        if !matches!(n.head, Head::Var(PROBE_IH)) {
            return Ok(None);
        }
        let mut spine: Vec<&Elim<'v>> = n.spine.iter_rev().collect();
        spine.reverse();
        if spine.len() != shape.modes.len() + slot.len() {
            return Ok(None);
        }
        for (proj, elim) in slot.iter().zip(&spine[shape.modes.len()..]) {
            let ok = matches!(
                (proj, elim),
                (Proj::Fst, Elim::Fst { .. }) | (Proj::Snd, Elim::Snd { .. })
            );
            if !ok {
                return Ok(None);
            }
        }
        self.state_of_call(&spine[..shape.modes.len()], shape)
    }

    /// The same argument check where the spine may continue: a finite or
    /// `Nat` output eliminates the recursive call further. Returns the
    /// eliminations past the call.
    fn call_arguments(
        &mut self,
        v: &Rc<Val<'v>>,
        shape: &Walk<'v>,
    ) -> Res<Option<Vec<&'v Elim<'v>>>> {
        let Val::Neutral(n) = &**v else { return Ok(None) };
        let mut spine: Vec<&'v Elim<'v>> = n.spine.iter_rev().collect();
        spine.reverse();
        if spine.len() < shape.modes.len() {
            return Ok(None);
        }
        if self.state_of_call(&spine[..shape.modes.len()], shape)?.is_none() {
            return Ok(None);
        }
        Ok(Some(spine[shape.modes.len()..].to_vec()))
    }

    /// Check the recursive call's arguments and read the state it carries:
    /// a peeled argument must be the probe's own tail variable inside the
    /// same wrapper, a carried one the probe's carried variable, and a state
    /// one an enumerated value.
    fn state_of_call(&mut self, apps: &[&Elim<'v>], shape: &Walk<'v>) -> Res<Option<u32>> {
        let mut index = 0usize;
        let mut radix = 1usize;
        for (j, mode) in shape.modes.iter().enumerate() {
            let Elim::App { arg, .. } = apps[j] else { return Ok(None) };
            let v = self.force(arg)?;
            let v = self.delta_whnf(v)?;
            match mode {
                ArgMode::Peeled(i) => {
                    let slot = shape.peeled[*i as usize].clone();
                    let Some(inner) = self.slot_of(&slot, Rc::clone(&v))? else {
                        return Ok(None);
                    };
                    if !is_var(&inner, PROBE_TAIL - *i) {
                        return Ok(None);
                    }
                }
                ArgMode::Carried => {
                    if !is_var(&v, PROBE_CARRIED - j as u32) {
                        return Ok(None);
                    }
                }
                ArgMode::State(i) => {
                    let Some(read) = self.read_enum(&v, NEST_LIMIT)? else { return Ok(None) };
                    let values = &shape.state_enums[*i as usize];
                    let Some(pos) = values.iter().position(|x| *x == read) else {
                        return Ok(None);
                    };
                    index += pos * radix;
                    radix *= values.len();
                }
            }
        }
        Ok(Some(index as u32))
    }

    // -----------------------------------------------------------------
    // The motive's Π-chain
    // -----------------------------------------------------------------

    /// Walk `M(len)`'s Π-chain, classifying each domain and choosing a probe
    /// value for it: a peeled argument gets `⟨bit, tailⱼ⟩` inside its
    /// wrapper, a state argument its chosen enumerated value, a carried one
    /// a fresh neutral. Later domains may mention earlier arguments
    /// (`concat`'s high half is a `BitVec(m)` over its own `m`), so the walk
    /// instantiates as it goes.
    fn walk_motive(
        &mut self,
        motive: &'v TyClo<'v>,
        len: &'v TmClo<'v>,
        bits: u32,
        state_choice: &[usize],
    ) -> Res<Option<Walk<'v>>> {
        let mut cur = self.apply_ty(motive, &[len])?;
        cur = self.delta_whnf_ty(cur)?;
        let mut modes = Vec::new();
        let mut peeled: Vec<Slot> = Vec::new();
        let mut state_enums: Vec<Vec<EnumVal>> = Vec::new();
        let mut args: Vec<&'v TmClo<'v>> = Vec::new();
        loop {
            let VTy::Pi { dom, cod, .. } = &*cur else { break };
            let (dom, cod) = (*dom, *cod);
            let index = args.len();
            let mode = self.argument_mode(dom)?;
            let arg = match mode {
                Mode::Peeled(at) => {
                    let i = peeled.len() as u32;
                    let Some(bt) = self.bit_ty(at.elem)? else { return Ok(None) };
                    let bit = (bits >> i) & 1 == 1;
                    let tail = self.transduce_var(PROBE_TAIL - i);
                    let Some(value) = self.peeled_probe(&at, bt, bit, tail)? else {
                        return Ok(None);
                    };
                    modes.push(ArgMode::Peeled(i));
                    peeled.push(at.slot);
                    value
                }
                Mode::State(values) => {
                    let i = state_enums.len();
                    let pick = state_choice.get(i).copied().unwrap_or(0) % values.len();
                    let Some(value) = self.enum_value(dom, &values[pick])? else {
                        return Ok(None);
                    };
                    modes.push(ArgMode::State(i as u32));
                    state_enums.push(values);
                    value
                }
                Mode::Carried => {
                    modes.push(ArgMode::Carried);
                    self.transduce_var(PROBE_CARRIED - index as u32)
                }
            };
            cur = self.apply_ty(cod, &[arg])?;
            cur = self.delta_whnf_ty(cur)?;
            args.push(arg);
        }
        let cod = self.arena.ty(TyClo::val(cur));
        Ok(Some(Walk { modes, peeled, state_enums, args, cod }))
    }

    fn argument_mode(&mut self, dom: &'v TyClo<'v>) -> Res<Mode<'v>> {
        // A vector at a *successor* length is peeled: it has a head bit to
        // read. One at an open length has none, so it is carried.
        if let Some(at) = self.vec_in(dom, NEST_LIMIT)? {
            // δ-transparently: an index written `m + k` is a *definition*
            // applied to the width, and it is a successor only after that
            // definition unfolds. The question is about the eliminator's own
            // annotation, decided once per class, so this is not a δ
            // discipline change — it is the same reading `bits.rs` makes of
            // an element type reached through `El` of a glued code.
            let len = self.force(at.len)?;
            let len = self.delta_whnf(len)?;
            if matches!(&*len, Val::Succ(_) | Val::NatRun { .. })
                && self.bit_ty(at.elem)?.is_some()
            {
                return Ok(Mode::Peeled(at));
            }
            return Ok(Mode::Carried);
        }
        if let Some(values) = self.enumerate(dom, NEST_LIMIT)? {
            return Ok(Mode::State(values));
        }
        Ok(Mode::Carried)
    }

    /// `⟨bit, tail⟩` at the vector, inside the argument's wrapper.
    fn peeled_probe(
        &mut self,
        at: &VecAt<'v>,
        bt: &'v BitTy<'v>,
        bit: bool,
        tail: &'v TmClo<'v>,
    ) -> Res<Option<&'v TmClo<'v>>> {
        let len = self.force(at.len)?;
        let len = self.delta_whnf(len)?;
        let pred = match &*len {
            Val::Succ(p) => *p,
            Val::NatRun { program, tail } => {
                Val::nat_run_pred(self.arena, program, tail)
            }
            _ => return Ok(None),
        };
        let inner = self.vclo(Rc::new(Val::Pair {
            ann: Some(SigAnn {
                fst_level: at.level.clone(),
                snd_level: at.level.clone(),
                fst_ty: at.elem,
                snd_ty: self.arena.ty_vec(at.level.clone(), at.elem, pred),
            }),
            fst: if bit { bt.one } else { bt.zero },
            snd: tail,
        }));
        let (outer, slot) = (at.outer, at.slot.clone());
        self.wrap_at(outer, &slot, inner)
    }

    // -----------------------------------------------------------------
    // Applying the step
    // -----------------------------------------------------------------

    fn transduce_apply(&mut self, step: &'v TmClo<'v>, args: &[&'v TmClo<'v>]) -> Res<Rc<Val<'v>>> {
        let ih = self.transduce_var(PROBE_IH);
        let k = self.transduce_var(PROBE_K);
        let mut v = self.drive(Work::Apply(step, vec![k, ih]))?;
        for arg in args {
            let app = self.dummy_app(arg);
            v = self.drive(Work::Elim(v, app))?;
        }
        self.delta_whnf(v)
    }

    /// An application whose annotations are dummies: the probe reads the
    /// result for its head and spine and never keeps it, exactly as
    /// `probe.rs`'s synchronous probe does.
    fn dummy_app(&self, arg: &'v TmClo<'v>) -> Elim<'v> {
        let nat = self.arena.ty(TyClo::new(Env::empty(), Rc::new(Type::Nat)));
        Elim::App {
            ann: Some(PiAnn {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: nat,
                cod: nat,
            }),
            arg,
        }
    }

    /// `Succ^q(t)` as `(q, t)`, `t` forced past every successor and glued
    /// definition.
    fn strip_run(&mut self, value: Rc<Val<'v>>) -> Res<(Increment, Rc<Val<'v>>)> {
        let mut inc: Increment = None;
        let mut cur = value;
        loop {
            let next = match &*cur {
                Val::Succ(pred) => {
                    inc = add_increments(&inc, &Some(ContextProgram::run((), ONE)));
                    *pred
                }
                Val::NatRun { program, tail } => {
                    inc = add_increments(&inc, &Some(Rc::clone(program)));
                    *tail
                }
                _ => return Ok((inc, cur)),
            };
            let forced = self.force(next)?;
            cur = self.delta_whnf(forced)?;
        }
    }

    // -----------------------------------------------------------------
    // Wrappers: finding, building and projecting the `Vec` in a type
    // -----------------------------------------------------------------

    /// The `Vec` this type *is*, without forcing it into its Σ-chain. A
    /// `Vec` at a canonical length whnfs to a Σ, so asking the whnf is not
    /// enough — and a record's Σ must not be mistaken for one.
    fn vec_view(&mut self, ty: &'v TyClo<'v>) -> Res<Option<VecAt<'v>>> {
        let found = match ty {
            TyClo::Vec { level, elem, len } => {
                Some(((*level).clone(), *elem as &'v TyClo<'v>, *len))
            }
            TyClo::Syn { env, body } => match &**body {
                Type::Vec { level, elem, len } => Some((
                    level.clone(),
                    self.arena.ty(TyClo::new(*env, Rc::clone(elem))),
                    self.arena.tm(TmClo::syn(*env, Rc::clone(len))),
                )),
                _ => None,
            },
            TyClo::Val(v) => match &**v {
                VTy::Vec { level, elem, len } => {
                    Some((level.clone(), *elem, self.vclo(Rc::clone(len))))
                }
                _ => None,
            },
            TyClo::El { level, tm } => {
                let v = self.force(tm)?;
                let v = self.delta_whnf(v)?;
                match &*v {
                    Val::TmVec { level: l, elem, len } => Some((
                        l.clone(),
                        self.arena.ty_el((*level).clone(), elem),
                        *len,
                    )),
                    _ => None,
                }
            }
        };
        Ok(found.map(|(level, elem, len)| VecAt {
            slot: Vec::new(),
            outer: ty,
            level,
            elem,
            len,
        }))
    }

    /// Where the `Vec` inside `ty` sits: the type itself, or one component
    /// of a Σ-nest whose other components are unit-like — a record
    /// (module doc). `None` for anything else.
    fn vec_in(&mut self, ty: &'v TyClo<'v>, depth: u32) -> Res<Option<VecAt<'v>>> {
        if let Some(at) = self.vec_view(ty)? {
            return Ok(Some(at));
        }
        if depth == 0 {
            return Ok(None);
        }
        let w = self.force_ty(ty)?;
        let w = self.delta_whnf_ty(w)?;
        let VTy::Sigma { fst_level, fst, snd, .. } = &*w else { return Ok(None) };
        let (fst, snd) = (*fst, *snd);
        let _ = fst_level;
        // A `Vec` at a successor length *is* this Σ: its tail is the
        // unforced `Vec` closure `Eval::vec_ty` built, over the same
        // element type. Recognizing it here is what keeps a vector reached
        // through an already-forced annotation from being read as a record.
        if let TyClo::Vec { level: l, elem, len: pred } = snd {
            if std::ptr::eq(*elem, fst) {
                let len = self.vclo(Rc::new(Val::Succ(pred)));
                return Ok(Some(VecAt {
                    slot: Vec::new(),
                    outer: ty,
                    level: (*l).clone(),
                    elem: fst,
                    len,
                }));
            }
        }
        if let Some(mut at) = self.vec_in(fst, depth - 1)? {
            at.slot.insert(0, Proj::Fst);
            at.outer = ty;
            return Ok(Some(at));
        }
        let Some(head) = self.unit_inhabitant(fst, UNIT_NEST_LIMIT)? else { return Ok(None) };
        let rest = self.apply_ty(snd, &[head])?;
        let rest = self.arena.ty(TyClo::val(rest));
        if let Some(mut at) = self.vec_in(rest, depth - 1)? {
            at.slot.insert(0, Proj::Snd);
            at.outer = ty;
            return Ok(Some(at));
        }
        Ok(None)
    }

    /// Rebuild a wrapper around `inner`, filling every component the slot
    /// does not pass through with its unit-like type's canonical inhabitant.
    /// `ty` is the *wrapped* type, so the Σ annotations are its own.
    fn wrap_at(
        &mut self,
        ty: &'v TyClo<'v>,
        slot: &[Proj],
        inner: &'v TmClo<'v>,
    ) -> Res<Option<&'v TmClo<'v>>> {
        let Some((step, rest)) = slot.split_first() else { return Ok(Some(inner)) };
        let w = self.force_ty(ty)?;
        let w = self.delta_whnf_ty(w)?;
        let VTy::Sigma { fst_level, snd_level, fst, snd } = &*w else { return Ok(None) };
        let (fst_level, snd_level, fst, snd) =
            (fst_level.clone(), snd_level.clone(), *fst, *snd);
        let (head, tail) = match step {
            Proj::Fst => {
                let Some(head) = self.wrap_at(fst, rest, inner)? else { return Ok(None) };
                let rest_ty = self.apply_ty(snd, &[head])?;
                let rest_ty = self.arena.ty(TyClo::val(rest_ty));
                let Some(tail) = self.unit_inhabitant(rest_ty, UNIT_NEST_LIMIT)? else {
                    return Ok(None);
                };
                (head, tail)
            }
            Proj::Snd => {
                let Some(head) = self.unit_inhabitant(fst, UNIT_NEST_LIMIT)? else {
                    return Ok(None);
                };
                let rest_ty = self.apply_ty(snd, &[head])?;
                let rest_ty = self.arena.ty(TyClo::val(rest_ty));
                let Some(tail) = self.wrap_at(rest_ty, rest, inner)? else { return Ok(None) };
                (head, tail)
            }
        };
        Ok(Some(self.vclo(Rc::new(Val::Pair {
            ann: Some(SigAnn { fst_level, snd_level, fst_ty: fst, snd_ty: snd }),
            fst: head,
            snd: tail,
        }))))
    }

    /// Project down a wrapper, checking that every component the slot does
    /// not pass through is the canonical inhabitant of a unit-like type.
    /// Purely on the value: a wrapper that is not built is not one this can
    /// see through, and declining is the caller's ordinary path.
    fn slot_of(&mut self, slot: &[Proj], v: Rc<Val<'v>>) -> Res<Option<Rc<Val<'v>>>> {
        let mut cur = v;
        for step in slot {
            let Val::Pair { fst, snd, .. } = &*cur else { return Ok(None) };
            let (fst, snd) = (*fst, *snd);
            let (keep, drop) = match step {
                Proj::Fst => (fst, snd),
                Proj::Snd => (snd, fst),
            };
            if !self.is_canonical_unit(drop, UNIT_NEST_LIMIT)? {
                return Ok(None);
            }
            let next = self.force(keep)?;
            cur = self.delta_whnf(next)?;
        }
        Ok(Some(cur))
    }

    /// The projection *closure* down a wrapper, annotated from the type it
    /// projects out of. Nothing is forced: this is the tail a produced run
    /// points at, and forcing it is what the run exists to avoid.
    fn slot_thunk(
        &mut self,
        ty: &'v TyClo<'v>,
        slot: &[Proj],
        c: &'v TmClo<'v>,
    ) -> Res<Option<&'v TmClo<'v>>> {
        let mut cur = c;
        let mut ty = ty;
        for step in slot {
            let w = self.force_ty(ty)?;
            let w = self.delta_whnf_ty(w)?;
            let VTy::Sigma { fst_level, snd_level, fst, snd } = &*w else { return Ok(None) };
            let (fst_level, snd_level, fst_ty, snd_ty) =
                (fst_level.clone(), snd_level.clone(), *fst, *snd);
            let fst_elim = Elim::Fst {
                ann: Some(SigAnn {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty,
                    snd_ty,
                }),
            };
            let next_ty = match step {
                Proj::Fst => fst_ty,
                Proj::Snd => {
                    let head = self.arena.tm(TmClo::elim(cur, Rc::new(fst_elim.clone())));
                    let t = self.apply_ty(snd_ty, &[head])?;
                    self.arena.ty(TyClo::val(t))
                }
            };
            let elim = match step {
                Proj::Fst => fst_elim,
                Proj::Snd => Elim::Snd {
                    ann: Some(SigAnn { fst_level, snd_level, fst_ty, snd_ty }),
                },
            };
            cur = self.arena.tm(TmClo::elim(cur, Rc::new(elim)));
            ty = next_ty;
        }
        Ok(Some(cur))
    }

    // -----------------------------------------------------------------
    // Finitely enumerable types
    // -----------------------------------------------------------------

    /// Every value of a *finitely enumerable* type — the bit criterion
    /// widened (design §4.1): `Unit` is one value, a `Sum` of enumerables
    /// the sum of theirs, a `Σ` of enumerables the product. `None` is "not
    /// enumerable, or more than [`STATE_CAP`] values".
    fn enumerate(&mut self, ty: &'v TyClo<'v>, depth: u32) -> Res<Option<Vec<EnumVal>>> {
        if depth == 0 {
            return Ok(None);
        }
        let w = self.force_ty(ty)?;
        let w = self.delta_whnf_ty(w)?;
        let out = match &*w {
            VTy::Unit { .. } => vec![EnumVal::Triv],
            VTy::Sum { lhs, rhs, .. } => {
                let (lhs, rhs) = (*lhs, *rhs);
                let (Some(l), Some(r)) =
                    (self.enumerate(lhs, depth - 1)?, self.enumerate(rhs, depth - 1)?)
                else {
                    return Ok(None);
                };
                l.into_iter()
                    .map(|v| EnumVal::Inl(Rc::new(v)))
                    .chain(r.into_iter().map(|v| EnumVal::Inr(Rc::new(v))))
                    .collect()
            }
            VTy::Sigma { fst, snd, .. } => {
                let (fst, snd) = (*fst, *snd);
                let Some(heads) = self.enumerate(fst, depth - 1)? else { return Ok(None) };
                let mut out = Vec::new();
                for head in heads {
                    let Some(hv) = self.enum_value(fst, &head)? else { return Ok(None) };
                    let rest = self.apply_ty(snd, &[hv])?;
                    let rest = self.arena.ty(TyClo::val(rest));
                    let Some(tails) = self.enumerate(rest, depth - 1)? else { return Ok(None) };
                    for tail in tails {
                        out.push(EnumVal::Pair(Rc::new(head.clone()), Rc::new(tail)));
                    }
                    if out.len() > crate::value::transducer::STATE_CAP as usize {
                        return Ok(None);
                    }
                }
                out
            }
            _ => return Ok(None),
        };
        if out.len() > crate::value::transducer::STATE_CAP as usize {
            return Ok(None);
        }
        Ok(Some(out))
    }

    /// The value an [`EnumVal`] stands for, at its type.
    fn enum_value(&mut self, ty: &'v TyClo<'v>, ev: &EnumVal) -> Res<Option<&'v TmClo<'v>>> {
        let w = self.force_ty(ty)?;
        let w = self.delta_whnf_ty(w)?;
        Ok(match (&*w, ev) {
            (VTy::Unit { level }, EnumVal::Triv) => {
                let level = level.clone();
                Some(self.vclo(Rc::new(Val::Triv { level })))
            }
            (VTy::Sum { lhs_level, rhs_level, lhs, rhs }, EnumVal::Inl(v) | EnumVal::Inr(v)) => {
                let (lhs_level, rhs_level, lhs, rhs) =
                    (lhs_level.clone(), rhs_level.clone(), *lhs, *rhs);
                let right = matches!(ev, EnumVal::Inr(_));
                let Some(val) = self.enum_value(if right { rhs } else { lhs }, v)? else {
                    return Ok(None);
                };
                let ann = Some(SumAnn { lhs_level, rhs_level, lhs, rhs });
                Some(self.vclo(Rc::new(if right {
                    Val::Inr { ann, val }
                } else {
                    Val::Inl { ann, val }
                })))
            }
            (VTy::Sigma { fst_level, snd_level, fst, snd }, EnumVal::Pair(a, b)) => {
                let (fst_level, snd_level, fst_ty, snd_ty) =
                    (fst_level.clone(), snd_level.clone(), *fst, *snd);
                let Some(head) = self.enum_value(fst_ty, a)? else { return Ok(None) };
                let rest = self.apply_ty(snd_ty, &[head])?;
                let rest = self.arena.ty(TyClo::val(rest));
                let Some(tail) = self.enum_value(rest, b)? else { return Ok(None) };
                Some(self.vclo(Rc::new(Val::Pair {
                    ann: Some(SigAnn { fst_level, snd_level, fst_ty, snd_ty }),
                    fst: head,
                    snd: tail,
                })))
            }
            _ => None,
        })
    }

    /// Read a computed value back as an [`EnumVal`]; `None` when it is not
    /// one of the enumerated shapes — a neutral payload, say, which is what
    /// keeps a non-canonical value from being read as a canonical one.
    fn read_enum(&mut self, v: &Rc<Val<'v>>, depth: u32) -> Res<Option<EnumVal>> {
        if depth == 0 {
            return Ok(None);
        }
        Ok(match &**v {
            Val::Triv { .. } => Some(EnumVal::Triv),
            Val::Inl { val, .. } | Val::Inr { val, .. } => {
                let right = matches!(&**v, Val::Inr { .. });
                let inner = self.force(val)?;
                let inner = self.delta_whnf(inner)?;
                let Some(read) = self.read_enum(&inner, depth - 1)? else { return Ok(None) };
                Some(if right {
                    EnumVal::Inr(Rc::new(read))
                } else {
                    EnumVal::Inl(Rc::new(read))
                })
            }
            Val::Pair { fst, snd, .. } => {
                let (fst, snd) = (*fst, *snd);
                let a = self.force(fst)?;
                let a = self.delta_whnf(a)?;
                let Some(a) = self.read_enum(&a, depth - 1)? else { return Ok(None) };
                let b = self.force(snd)?;
                let b = self.delta_whnf(b)?;
                let Some(b) = self.read_enum(&b, depth - 1)? else { return Ok(None) };
                Some(EnumVal::Pair(Rc::new(a), Rc::new(b)))
            }
            _ => None,
        })
    }
}

/// The combinations, as `(bits, state indices)` pairs in table order.
fn combinations(
    state_enums: &[Vec<EnumVal>],
    peeled: u32,
    states: usize,
) -> Vec<(u32, Vec<usize>)> {
    let mut out = Vec::with_capacity(states << peeled);
    for s in 0..states {
        let mut rest = s;
        let mut choice = Vec::with_capacity(state_enums.len());
        for e in state_enums {
            choice.push(rest % e.len());
            rest /= e.len();
        }
        for bits in 0..(1u32 << peeled) {
            out.push((bits, choice.clone()));
        }
    }
    out
}

/// The state enumeration in table-index order: the mixed-radix product of
/// the state arguments' own enumerations.
fn state_values(state_enums: &[Vec<EnumVal>]) -> Vec<EnumVal> {
    if state_enums.is_empty() {
        return vec![EnumVal::Triv];
    }
    let states: usize = state_enums.iter().map(Vec::len).product();
    let mut out = Vec::with_capacity(states);
    for s in 0..states {
        let mut rest = s;
        let mut acc: Option<EnumVal> = None;
        for e in state_enums {
            let v = e[rest % e.len()].clone();
            rest /= e.len();
            acc = Some(match acc {
                None => v,
                Some(a) => EnumVal::Pair(Rc::new(a), Rc::new(v)),
            });
        }
        out.push(acc.unwrap_or(EnumVal::Triv));
    }
    out
}

fn is_var(v: &Rc<Val<'_>>, level: u32) -> bool {
    matches!(&**v, Val::Neutral(n) if matches!(n.head, Head::Var(l) if l == level)
        && n.spine.is_empty())
}

const ONE: std::num::NonZeroU64 = match std::num::NonZeroU64::new(1) {
    Some(one) => one,
    None => unreachable!(),
};

const _: () = assert!(BIT_RUN_WIDTH_CAP == 64);

// ---------------------------------------------------------------------------
// Running a classified fold
// ---------------------------------------------------------------------------

impl<'a, 'v> Eval<'a, 'v> {
    /// `elim_Nat(M; b; s; Succ^program(tail))` with `s` a transducer.
    ///
    /// The result is a *function* whenever the motive is a Π — which is
    /// every bitvector operation — so the fold cannot produce a word until
    /// its arguments arrive. [`Val::BitFold`] is that waiting value, exactly
    /// as [`Val::NatSync`] is for the synchronous `Nat` class; it collects
    /// applications and fires at the arity the class says. A motive with no
    /// binders (`zero`, `all_ones`: a word from a closed width alone) fires
    /// at once, because there is nothing to wait for and a value that is not
    /// a function must not be left opaque.
    pub(super) fn fold_transduce(
        &mut self,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimNat { motive, step, .. } = e else {
            unreachable!("fold_transduce is given a Nat eliminator")
        };
        // A fold whose motive is written `Nat` has no vector to read and
        // none to produce, whatever its step does: it is an ordinary `Nat`
        // fold that `probe.rs` has just declined, and the memo lookup below
        // is a hash of five words on the step of every such fold. This is a
        // fact about the eliminator's annotation, not a definition's
        // spelling; a motive that only *reduces* to `Nat` still consults the
        // memo, and merely later.
        if let Some((_, body)) = motive.as_syn() {
            if matches!(&**body, Type::Nat) {
                return Ok(None);
            }
        }
        let Some(class) = self.classify_transducer(step, motive)? else {
            return Ok(None);
        };
        if class.modes.is_empty() {
            return self.fire_transducer(program, tail, e, &class, &[]);
        }
        Ok(Some(Work::Val(Rc::new(Val::BitFold {
            program: Rc::clone(program),
            tail,
            elim: Rc::new(e.clone()),
            class,
            apps: Rc::new(Vec::new()),
        }))))
    }

    /// One application of a waiting fold: collect it, and fire at arity.
    pub(super) fn bit_fold_app(&mut self, head: &Rc<Val<'v>>, e: Elim<'v>) -> Res<Work<'v>> {
        let Val::BitFold { program, tail, elim, class, apps } = &**head else {
            unreachable!("bit_fold_app is given a waiting fold")
        };
        let mut collected = (**apps).clone();
        collected.push(Rc::new(e));
        if collected.len() < class.modes.len() {
            return Ok(Work::Val(Rc::new(Val::BitFold {
                program: Rc::clone(program),
                tail,
                elim: Rc::clone(elim),
                class: Rc::clone(class),
                apps: Rc::new(collected),
            })));
        }
        let (program, tail, elim, class) =
            (Rc::clone(program), *tail, Rc::clone(elim), Rc::clone(class));
        if let Some(work) = self.fire_transducer(&program, tail, &elim, &class, &collected)? {
            return Ok(work);
        }
        // Declined — an argument that does not pack, a state that does not
        // read back. Take the ordinary outer step and replay the
        // applications on its result: exactly the path this value stood in
        // for, and the one a fold that never classified takes today.
        let Elim::ElimNat { step, .. } = &*elim else {
            unreachable!("a waiting fold stores a Nat eliminator")
        };
        let step = *step;
        let pred = Val::nat_run_pred(self.arena, &program, tail);
        let ih = self.arena.tm(TmClo::elim(pred, Rc::clone(&elim)));
        for app in collected.iter().rev() {
            self.frames.push(super::Frame::Elim(Rc::clone(app)));
        }
        self.spend()?;
        Ok(Work::Apply(step, vec![pred, ih]))
    }

    /// Run the machine over the word (design §4.3): `width` bits taken off
    /// the run, the arguments packed, the table iterated, and the fold at
    /// the residual width left as the produced run's **tail** — unforced,
    /// which is what makes a chain of shape operations cost its last step
    /// and not its whole history.
    fn fire_transducer(
        &mut self,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        e: &Elim<'v>,
        class: &Rc<Transducer>,
        apps: &[Rc<Elim<'v>>],
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimNat { motive, .. } = e else { unreachable!() };
        let motive = *motive;
        // -- how many bits this run holds, and what is left over
        let cap = u64::from(BIT_RUN_WIDTH_CAP);
        let (width, residual) = match ContextProgram::repetition_count_up_to(program, cap) {
            Some(c) => (c as u32, None),
            None => {
                // Wider than one word: the design's §13 answer is a second
                // run over the first's tail, so take a word's worth and
                // leave the rest as the width of the fold at the tail.
                let mut rest = Rc::clone(program);
                for _ in 0..BIT_RUN_WIDTH_CAP {
                    let (_, next) = ContextProgram::uncons(&rest);
                    let Some(next) = next else { return Ok(None) };
                    rest = next;
                }
                (BIT_RUN_WIDTH_CAP, Some(rest))
            }
        };
        if width == 0 {
            return Ok(None);
        }

        let mut args: Vec<&'v TmClo<'v>> = Vec::with_capacity(apps.len());
        for app in apps {
            let Elim::App { arg, .. } = &**app else {
                return Ok(None);
            };
            args.push(*arg);
        }

        // -- the peeled arguments, as words
        let mut words = vec![0u64; class.peeled as usize];
        let mut rests: Vec<Option<Rc<Val<'v>>>> = vec![None; class.peeled as usize];
        let mut start = vec![0usize; class.state_enums.len()];
        // A finite output may short-circuit, so its bits are read one at a
        // time and only as far as the table needs them; every other output
        // consumes the whole word and takes it in bulk.
        let finite = matches!(class.output, Output::Finite { .. });
        let mut read = width;
        for (j, mode) in class.modes.iter().enumerate() {
            match mode {
                ArgMode::Peeled(i) => {
                    let v = self.force(args[j])?;
                    let v = self.delta_whnf(v)?;
                    let slot = class.slots[*i as usize].clone();
                    let Some(vector) = self.slot_of(&slot, v)? else {
                        return Ok(None);
                    };
                    rests[*i as usize] = Some(vector);
                }
                ArgMode::State(i) => {
                    let v = self.force(args[j])?;
                    let v = self.delta_whnf(v)?;
                    let Some(read) = self.read_enum(&v, NEST_LIMIT)? else {
                        return Ok(None);
                    };
                    let Some(pos) =
                        class.state_enums[*i as usize].iter().position(|x| *x == read)
                    else {
                        return Ok(None);
                    };
                    start[*i as usize] = pos;
                }
                ArgMode::Carried => {}
            }
        }
        let state0 = mixed_radix(&start, &class.state_enums);

        // -- the bits, and the machine over them
        if finite {
            // Read bits until the table stops caring about what is above
            // them, which is where the structural path stopped too.
            let mut taken = 0u32;
            'bits: while taken < width {
                let mut col = 0u32;
                for i in 0..class.peeled as usize {
                    let cur = rests[i].take().expect("a peeled argument");
                    let Some((bit, next)) = self.pack_bit(cur)? else {
                        return Ok(None);
                    };
                    col |= u32::from(bit) << i;
                    words[i] |= u64::from(bit) << taken;
                    rests[i] = Some(next);
                }
                taken += 1;
                if class.finite_constant(col as usize).is_some() {
                    break 'bits;
                }
            }
            read = taken;
        } else {
            for i in 0..class.peeled as usize {
                let cur = rests[i].take().expect("a peeled argument");
                let Some((word, next)) = self.pack_word(cur, width)? else {
                    return Ok(None);
                };
                words[i] = word;
                rests[i] = Some(next);
            }
        }
        // One unit per bit (design §8), charged once the fold is known to
        // fire: strictly less than the structural path spends on the same
        // bits, so no verdict fuel allows today becomes a refusal — and an
        // attempt that declines has not spent the word's worth twice.
        self.spend_n(u64::from(read))?;

        let (produced, end_state) = match &class.output {
            Output::Cons { .. } => {
                let Some(out) = class.run_cons(width, &words, state0) else { return Ok(None) };
                out
            }
            Output::Pass => (0, class.run_pass(width, &words, state0)),
            Output::Finite { .. } | Output::Scaled { .. } => (0, state0),
        };
        // A finite fold that settled early never needs the fold at the tail,
        // and must not build it: that is the early exit the structural path
        // had and this one would otherwise have lost.
        if finite && read < width {
            let Some((out, _)) = class.run_finite_short(read, &words, None) else {
                return Ok(None);
            };
            return self.finite_value(motive, program, tail, &args, class, out);
        }

        // -- the fold at the residual width, at the residual arguments
        let tail_len = match &residual {
            None => tail,
            Some(p) => self.vclo(Rc::new(Val::NatRun { program: Rc::clone(p), tail })),
        };
        let end = decompose(end_state, &class.state_enums);
        let mut cur = self.apply_ty(motive, &[tail_len])?;
        cur = self.delta_whnf_ty(cur)?;
        let mut residual_apps: Vec<Rc<Elim<'v>>> = Vec::with_capacity(class.modes.len());
        for (j, mode) in class.modes.iter().enumerate() {
            let VTy::Pi { dom_level, cod_level, dom, cod } = &*cur else {
                return Ok(None);
            };
            let (dom_level, cod_level, dom, cod) =
                (dom_level.clone(), cod_level.clone(), *dom, *cod);
            let arg = match mode {
                ArgMode::Peeled(i) => {
                    let inner = self.vclo(rests[*i as usize].clone().expect("packed"));
                    let slot = class.slots[*i as usize].clone();
                    let Some(a) = self.wrap_at(dom, &slot, inner)? else {
                        return Ok(None);
                    };
                    a
                }
                ArgMode::State(i) => {
                    let value = class.state_enums[*i as usize][end[*i as usize]].clone();
                    let Some(a) = self.enum_value(dom, &value)? else { return Ok(None) };
                    a
                }
                ArgMode::Carried => args[j],
            };
            residual_apps.push(Rc::new(Elim::App { ann: Some(PiAnn { dom_level, cod_level, dom, cod }), arg }));
            cur = self.apply_ty(cod, &[arg])?;
            cur = self.delta_whnf_ty(cur)?;
        }
        let cod_at_tail = self.arena.ty(TyClo::val(cur));
        let mut folded = self.arena.tm(TmClo::elim(tail_len, Rc::new(e.clone())));
        for app in &residual_apps {
            folded = self.arena.tm(TmClo::elim(folded, Rc::clone(app)));
        }

        match &class.output {
            Output::Pass => Ok(Some(Work::Force(folded))),
            Output::Cons { .. } => {
                let Some(at) = self.vec_in(cod_at_tail, NEST_LIMIT)? else {
                    return Ok(None);
                };
                let Some(bt) = self.bit_ty(at.elem)? else {
                    return Ok(None);
                };
                let slot = class.out_slot.clone();
                let Some(run_tail) = self.slot_thunk(cod_at_tail, &slot, folded)? else {
                    return Ok(None);
                };
                let run = self.vclo(Rc::new(Val::BitRun {
                    level: at.level.clone(),
                    ty: bt,
                    width,
                    bits: produced,
                    tail_len: at.len,
                    tail: run_tail,
                }));
                let full = self.vclo(Rc::new(Val::NatRun {
                    program: Rc::clone(program),
                    tail,
                }));
                let Some(out_ty) = self.codomain_at(motive, full, &args)? else {
                    return Ok(None);
                };
                let Some(value) = self.wrap_at(out_ty, &slot, run)? else {
                    return Ok(None);
                };
                Ok(Some(Work::Force(value)))
            }
            Output::Finite { values, .. } => {
                let base = self.force(folded)?;
                let base = self.delta_whnf(base)?;
                let Some(seen) = self.read_enum(&base, NEST_LIMIT)? else { return Ok(None) };
                let Some(index) = values.iter().position(|v| *v == seen) else {
                    return Ok(None);
                };
                let Some((out, _)) =
                    class.run_finite_short(width, &words, Some(index as u32))
                else {
                    return Ok(None);
                };
                self.finite_value(motive, program, tail, &args, class, out)
            }
            Output::Scaled { .. } => {
                let base = self.force(folded)?;
                let base = self.delta_whnf(base)?;
                let (base_inc, under) = self.strip_run(base)?;
                let Some((q, r)) = class.run_scaled(width, &words, state0) else {
                    return Ok(None);
                };
                // `q·base + r` is a run over `base`'s own tail only when the
                // coefficient is one or the base is closed; anything else is
                // a multiplication of an *open* term, which a run cannot
                // spell. Declining leaves the ordinary fold, as everywhere.
                let closed = matches!(&*under, Val::Zero);
                let unit = q.is_none()
                    || matches!(q.as_deref(),
                        Some(ContextProgram::Run { count, .. }) if count.get() == 1);
                if !closed && !unit {
                    return Ok(None);
                }
                let total = add_increments(&scale(&q, &base_inc), &r);
                let under = self.vclo(under);
                Ok(Some(Work::Val(match total {
                    None => Rc::new(Val::Zero),
                    Some(program) => Rc::new(Val::NatRun { program, tail: under }),
                })))
            }
        }
    }

    /// The value a finite output settled on, at the fold's own result type.
    fn finite_value(
        &mut self,
        motive: &'v TyClo<'v>,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        args: &[&'v TmClo<'v>],
        class: &Rc<Transducer>,
        out: u32,
    ) -> Res<Option<Work<'v>>> {
        let Output::Finite { values, .. } = &class.output else { return Ok(None) };
        let value = values[out as usize].clone();
        let full = self.vclo(Rc::new(Val::NatRun {
            program: Rc::clone(program),
            tail,
        }));
        let Some(out_ty) = self.codomain_at(motive, full, args)? else { return Ok(None) };
        let Some(v) = self.enum_value(out_ty, &value)? else { return Ok(None) };
        Ok(Some(Work::Force(v)))
    }

    /// One bit off the head of a vector value, and what is left of it.
    fn pack_bit(&mut self, value: Rc<Val<'v>>) -> Res<Option<(bool, Rc<Val<'v>>)>> {
        Ok(self.pack_word(value, 1)?.map(|(bits, rest)| (bits & 1 == 1, rest)))
    }

    /// The first `width` bits of a vector value, and what is left of it.
    ///
    /// A run gives its bits in bulk — which is what makes a chain of
    /// operations cost one machine word per operation rather than one walk
    /// per bit — and a structural chain gives them one pair at a time.
    /// Anything else declines, and declining is the fold this replaced.
    fn pack_word(
        &mut self,
        value: Rc<Val<'v>>,
        width: u32,
    ) -> Res<Option<(u64, Rc<Val<'v>>)>> {
        let mut bits = 0u64;
        let mut taken = 0u32;
        let mut cur = value;
        while taken < width {
            let next = match &*cur {
                Val::BitRun { level, ty, width: held, bits: word, tail_len, tail } => {
                    let take = (*held).min(width - taken);
                    bits |= (word & mask(take)) << taken;
                    taken += take;
                    if take == *held {
                        let tail = *tail;
                        let forced = self.force(tail)?;
                        self.delta_whnf(forced)?
                    } else {
                        Rc::new(Val::BitRun {
                            level: level.clone(),
                            ty,
                            width: held - take,
                            bits: word >> take,
                            tail_len: *tail_len,
                            tail: *tail,
                        })
                    }
                }
                Val::Pair { fst, snd, .. } => {
                    let (fst, snd) = (*fst, *snd);
                    let head = self.force(fst)?;
                    let head = self.delta_whnf(head)?;
                    let Some(bit) = self.bit_of(&head)? else { return Ok(None) };
                    bits |= u64::from(bit) << taken;
                    taken += 1;
                    let rest = self.force(snd)?;
                    self.delta_whnf(rest)?
                }
                _ => return Ok(None),
            };
            cur = next;
        }
        Ok(Some((bits, cur)))
    }

    /// `M(len) a⃗`'s codomain, the arguments applied in order.
    fn codomain_at(
        &mut self,
        motive: &'v TyClo<'v>,
        len: &'v TmClo<'v>,
        args: &[&'v TmClo<'v>],
    ) -> Res<Option<&'v TyClo<'v>>> {
        let mut cur = self.apply_ty(motive, &[len])?;
        cur = self.delta_whnf_ty(cur)?;
        for arg in args {
            let VTy::Pi { cod, .. } = &*cur else { return Ok(None) };
            let cod = *cod;
            cur = self.apply_ty(cod, &[arg])?;
            cur = self.delta_whnf_ty(cur)?;
        }
        Ok(Some(self.arena.ty(TyClo::val(cur))))
    }
}

fn mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// A state index from the state arguments' own positions, and back.
fn mixed_radix(positions: &[usize], enums: &[Vec<EnumVal>]) -> u32 {
    let mut index = 0usize;
    let mut radix = 1usize;
    for (pos, values) in positions.iter().zip(enums) {
        index += pos * radix;
        radix *= values.len();
    }
    index as u32
}

fn decompose(index: u32, enums: &[Vec<EnumVal>]) -> Vec<usize> {
    let mut rest = index as usize;
    let mut out = Vec::with_capacity(enums.len());
    for values in enums {
        out.push(rest % values.len());
        rest /= values.len();
    }
    out
}

#[cfg(test)]
mod tests {
    //! The design's verification items §§11.4–11.6, and the fold they
    //! license, on terms built the way the *library* builds them: a `Vec`
    //! inside a record, a bit that is an injection over a proof-irrelevant
    //! tag, and a step that case-splits on the head bit — which is what
    //! makes the uniform pass fail and the tabulated one necessary.
    //!
    //! Nothing here imports the library. The shapes are reconstructed by
    //! hand, as `tests/bitvec_values.rs` reconstructs them for the
    //! criterion, so the file stays a kernel test; the library's own
    //! `bxor`/`add`/`toNat` are measured end to end by the certificate.

    use super::*;
    use crate::reduce::Defs;
    use crate::term::{CtxBase, LocalVar, Term};
    use crate::value::transducer::Output;
    use crate::value::{Env, ValueArena};

    const FUEL: u64 = 4_000_000;

    // -- the shapes --------------------------------------------------------

    fn unit_ty() -> Rc<Type> {
        Rc::new(Type::Unit { level: Level::Zero })
    }

    fn triv() -> Rc<Term> {
        Rc::new(Term::Triv { level: Level::Zero })
    }

    fn sigma(fst: Rc<Type>, snd: Rc<Type>) -> Rc<Type> {
        Rc::new(Type::Sigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst,
            snd,
        })
    }

    fn pair(fst_ty: Rc<Type>, snd_ty: Rc<Type>, fst: Rc<Term>, snd: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Pair {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty,
            snd_ty,
            fst,
            snd,
        })
    }

    fn fst(fst_ty: Rc<Type>, snd_ty: Rc<Type>, p: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Fst {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty,
            snd_ty,
            pair: p,
        })
    }

    fn snd(fst_ty: Rc<Type>, snd_ty: Rc<Type>, p: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Snd {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty,
            snd_ty,
            pair: p,
        })
    }

    /// `Tag_D`: a Σ-nest of `Unit`s, proof-irrelevant and not `Unit` itself.
    fn tag() -> Rc<Type> {
        sigma(unit_ty(), unit_ty())
    }

    fn tag_value() -> Rc<Term> {
        pair(unit_ty(), unit_ty(), triv(), triv())
    }

    /// A nullary constructor's field spine.
    fn arm() -> Rc<Type> {
        sigma(tag(), unit_ty())
    }

    fn arm_value() -> Rc<Term> {
        pair(tag(), unit_ty(), tag_value(), triv())
    }

    fn bool_ty() -> Rc<Type> {
        Rc::new(Type::Sum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: arm(),
            rhs: arm(),
        })
    }

    fn bit(b: bool) -> Rc<Term> {
        let (lhs, rhs, val) = (arm(), arm(), arm_value());
        Rc::new(if b {
            Term::Inr { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs, rhs, val }
        } else {
            Term::Inl { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs, rhs, val }
        })
    }

    fn vec_ty(len: &Rc<Term>) -> Rc<Type> {
        Rc::new(Type::Vec { level: Level::Zero, elem: bool_ty(), len: Rc::clone(len) })
    }

    fn up(t: &Rc<Term>) -> Rc<Term> {
        Rc::new(t.shift_local(1))
    }

    /// `record BitVec(n) { bits: [Bool; n] }` — the library's wrapper.
    fn bv(len: &Rc<Term>) -> Rc<Type> {
        sigma(tag(), sigma(vec_ty(&up(len)), unit_ty()))
    }

    fn record(len: &Rc<Term>, bits: Rc<Term>) -> Rc<Term> {
        pair(
            tag(),
            sigma(vec_ty(&up(len)), unit_ty()),
            tag_value(),
            pair(vec_ty(len), unit_ty(), bits, triv()),
        )
    }

    fn bits_of(len: &Rc<Term>, t: Rc<Term>) -> Rc<Term> {
        fst(
            vec_ty(len),
            unit_ty(),
            snd(tag(), sigma(vec_ty(&up(len)), unit_ty()), t),
        )
    }

    /// Head, tail and cons of a vector at length `Succ len`.
    fn vhead(len: &Rc<Term>, v: Rc<Term>) -> Rc<Term> {
        fst(bool_ty(), vec_ty(&up(len)), v)
    }

    fn vtail(len: &Rc<Term>, v: Rc<Term>) -> Rc<Term> {
        snd(bool_ty(), vec_ty(&up(len)), v)
    }

    fn vcons(len: &Rc<Term>, b: Rc<Term>, rest: Rc<Term>) -> Rc<Term> {
        pair(bool_ty(), vec_ty(&up(len)), b, rest)
    }

    fn var(i: u32) -> Rc<Term> {
        Rc::new(Term::Var(LocalVar(i)))
    }

    fn succ(t: &Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Succ(Rc::clone(t)))
    }

    fn app(fun: Rc<Term>, dom: Rc<Type>, arg: Rc<Term>) -> Rc<Term> {
        let cod = Rc::new(dom.shift_local(1));
        Rc::new(Term::App {
            fun,
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom,
            cod,
            arg,
        })
    }

    fn lam(dom: Rc<Type>, body: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom,
            body,
        })
    }

    /// `match b { False => l, True => r }` at a `Bool`-shaped sum. The
    /// branches bind the (irrelevant) payload, so they are shifted.
    fn case(scrut: Rc<Term>, motive: Rc<Type>, l: Rc<Term>, r: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Case {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            motive_level: Level::Zero,
            lhs: arm(),
            rhs: arm(),
            motive,
            case_l: Rc::new(l.shift_local(1)),
            case_r: Rc::new(r.shift_local(1)),
            scrut,
        })
    }

    fn not_bit(b: Rc<Term>) -> Rc<Term> {
        case(b, bool_ty(), bit(true), bit(false))
    }

    /// `xor_bit(a, b)` as the library writes it: a case split on the first
    /// bit, which is exactly why the uniform pass cannot classify it.
    fn xor_bit(a: Rc<Term>, b: Rc<Term>) -> Rc<Term> {
        case(a, bool_ty(), Rc::clone(&b), not_bit(b))
    }

    // -- the steps ---------------------------------------------------------

    /// The motive `λ n. BitVec(n) → … → BitVec(n)`, `extra` `Bool`
    /// arguments appended after the vectors.
    fn motive(vectors: u32, states: u32, result: Option<()>) -> Rc<Type> {
        // Built inside out: the codomain sits under `vectors + states`
        // binders, so `n` climbs as the chain is built.
        let total = vectors + states;
        let mut out = match result {
            Some(()) => bv(&var(total)),
            None => Rc::new(Type::Nat),
        };
        for i in (0..total).rev() {
            let dom = if i < vectors { bv(&var(i)) } else { bool_ty() };
            out = Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom,
                cod: out,
            });
        }
        out
    }

    /// `bxor`'s step: two peeled vectors, no state, one bit out.
    fn xor_step() -> Rc<Term> {
        // Scope in the body: y = 0, x = 1, ih = 2, k = 3.
        let k = var(3);
        let xb = bits_of(&succ(&k), var(1));
        let yb = bits_of(&succ(&k), var(0));
        let call = app(
            app(var(2), bv(&k), record(&k, vtail(&k, Rc::clone(&xb)))),
            bv(&k),
            record(&k, vtail(&k, Rc::clone(&yb))),
        );
        let out = xor_bit(vhead(&k, xb), vhead(&k, yb));
        let body = record(&succ(&k), vcons(&k, out, bits_of(&k, call)));
        lam(bv(&succ(&var(1))), lam(bv(&succ(&var(2))), body))
    }

    /// `add_bits`' step: two peeled vectors and a carry, with the carry
    /// **forced before the recursive call** — `add_bits_next`'s `match`,
    /// inlined — which is §11.4's claim about the closed carry.
    fn add_step() -> Rc<Term> {
        // Scope in the body: carry = 0, y = 1, x = 2, ih = 3, k = 4.
        let k = var(4);
        let xb = bits_of(&succ(&k), var(2));
        let yb = bits_of(&succ(&k), var(1));
        let (hx, hy, carry) = (vhead(&k, Rc::clone(&xb)), vhead(&k, Rc::clone(&yb)), var(0));
        // sum = x ⊕ y ⊕ carry; majority = at least two of three.
        let sum = xor_bit(xor_bit(Rc::clone(&hx), Rc::clone(&hy)), Rc::clone(&carry));
        let majority = case(
            Rc::clone(&hx),
            bool_ty(),
            // x false: carry out iff y and carry.
            case(Rc::clone(&hy), bool_ty(), bit(false), Rc::clone(&carry)),
            // x true: carry out iff y or carry.
            case(Rc::clone(&hy), bool_ty(), Rc::clone(&carry), bit(true)),
        );
        let call = |c: Rc<Term>| {
            app(
                app(
                    app(var(3), bv(&k), record(&k, vtail(&k, Rc::clone(&xb)))),
                    bv(&k),
                    record(&k, vtail(&k, Rc::clone(&yb))),
                ),
                bool_ty(),
                c,
            )
        };
        let rest = case(majority, bv(&k), call(bit(false)), call(bit(true)));
        let body = record(&succ(&k), vcons(&k, sum, bits_of(&k, rest)));
        lam(
            bv(&succ(&var(1))),
            lam(bv(&succ(&var(2))), lam(bool_ty(), body)),
        )
    }

    /// `set`'s step: the index is a `Fin` at an open width, so it is
    /// neither a bit of a peeled argument nor a value of a bounded state
    /// type, and the step is stuck on a case split the probe cannot
    /// instantiate (design §4.4, §11.5).
    fn set_step() -> Rc<Term> {
        // Scope in the body: i = 0, x = 1, ih = 2, k = 3.
        let k = var(3);
        let xb = bits_of(&succ(&k), var(1));
        let call = app(
            app(var(2), bv(&k), record(&k, vtail(&k, Rc::clone(&xb)))),
            Rc::new(Type::Fin { len: Rc::new(k.shift_local(0)) }),
            var(0),
        );
        let zero_case = record(&succ(&k), vcons(&k, bit(true), bits_of(&k, Rc::clone(&xb))));
        let succ_case = record(
            &succ(&k),
            vcons(&k, vhead(&k, Rc::clone(&xb)), bits_of(&k, call)),
        );
        let body = Rc::new(Term::Case {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            motive_level: Level::Zero,
            lhs: unit_ty(),
            rhs: Rc::new(Type::Fin { len: Rc::clone(&k) }),
            motive: bv(&succ(&k)),
            case_l: Rc::new(zero_case.shift_local(1)),
            case_r: Rc::new(succ_case.shift_local(1)),
            scrut: var(0),
        });
        lam(
            bv(&succ(&var(1))),
            lam(Rc::new(Type::Fin { len: succ(&var(2)) }), body),
        )
    }

    /// `toNat`'s step: `bit_value(head) + twice(ih(tail))`, spelled as the
    /// two affine `Nat` folds the library's `add` and `twice` are.
    fn to_nat_step() -> Rc<Term> {
        // Scope in the body: x = 0, ih = 1, k = 2.
        let k = var(2);
        let xb = bits_of(&succ(&k), var(0));
        let call = app(var(1), bv(&k), record(&k, vtail(&k, Rc::clone(&xb))));
        // `twice(n)`: elim_Nat over `n`, step `su (su ih)`. An eliminator's
        // step is a body in the scope `(Γ, k, ih)` — the binders are the
        // rule's, not λ's — so `ih` is index 0.
        let twice = Rc::new(Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Zero),
            step: Rc::new(Term::Succ(Rc::new(Term::Succ(var(0))))),
            scrut: call,
        });
        // `add(a, b)`: elim_Nat over `b`, base `a`, step `su ih`.
        let value = case(vhead(&k, xb), Rc::new(Type::Nat), Rc::new(Term::Zero), {
            Rc::new(Term::Succ(Rc::new(Term::Zero)))
        });
        let body = Rc::new(Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: value,
            step: Rc::new(Term::Succ(var(0))),
            scrut: twice,
        });
        lam(bv(&succ(&var(1))), body)
    }


    // -- the fold the class licenses --------------------------------------

    /// `[b₀, …, b_{w-1}]` as the right-nested Σ the `Vec` rule builds.
    fn word(width: u32, bits: u128) -> Rc<Term> {
        let mut out = triv();
        for i in (0..width).rev() {
            out = vcons(&nat(u64::from(width - 1 - i)), bit(bits >> i & 1 == 1), out);
        }
        out
    }

    fn nat(n: u64) -> Rc<Term> {
        let mut t = Rc::new(Term::Zero);
        for _ in 0..n {
            t = Rc::new(Term::Succ(t));
        }
        t
    }

    fn dummy_ty<'v>(arena: &'v ValueArena<'v>) -> &'v TyClo<'v> {
        arena.ty(TyClo::new(Env::empty(), Rc::new(Type::Nat)))
    }

    /// Run `elim_Nat(M; base; step; Succ^width(0))` at `args`, and hand back
    /// the value.
    fn fold<'v>(
        arena: &'v ValueArena<'v>,
        motive_ty: Rc<Type>,
        base: Rc<Term>,
        step: Rc<Term>,
        width: u64,
        args: &[Rc<Term>],
    ) -> Rc<Val<'v>> {
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, arena);
        let elim = Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(Env::empty(), motive_ty)),
            base: arena.tm(TmClo::syn(Env::empty(), base)),
            step: arena.tm(TmClo::syn(Env::empty(), step)),
        };
        let zero = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let scrut = Rc::new(match std::num::NonZeroU64::new(width) {
            None => Val::Zero,
            Some(c) => Val::NatRun { program: ContextProgram::run((), c), tail: zero },
        });
        let mut v = ev.elim(scrut, elim).expect("fuel");
        for arg in args {
            let a = arena.tm(TmClo::syn(Env::empty(), Rc::clone(arg)));
            let app = Elim::App {
                ann: Some(PiAnn {
                    dom_level: Level::Zero,
                    cod_level: Level::Zero,
                    dom: dummy_ty(arena),
                    cod: dummy_ty(arena),
                }),
                arg: a,
            };
            v = ev.elim(v, app).expect("fuel");
        }
        v
    }

    /// The word a produced value holds, at the record's slot.
    fn produced<'v>(arena: &'v ValueArena<'v>, v: Rc<Val<'v>>) -> (u32, u64) {
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, arena);
        let inner = ev
            .slot_of(&[Proj::Snd, Proj::Fst], v)
            .expect("fuel")
            .expect("a record");
        match &*inner {
            Val::BitRun { width, bits, .. } => (*width, *bits),
            other => panic!("not a run: {other:?}"),
        }
    }

    #[test]
    fn a_classified_xor_produces_one_word() {
        let arena = ValueArena::new();
        let base = lam(bv(&nat(0)), lam(bv(&nat(0)), record(&nat(0), triv())));
        let (a, b) = (0xa5u64, 0x3cu64);
        let v = fold(
            &arena,
            motive(2, 0, Some(())),
            base,
            xor_step(),
            8,
            &[record(&nat(8), word(8, u128::from(a))), record(&nat(8), word(8, u128::from(b)))],
        );
        assert_eq!(produced(&arena, v), (8, a ^ b));
    }

    #[test]
    fn a_classified_add_threads_its_carry_over_the_whole_word() {
        let arena = ValueArena::new();
        let base = lam(
            bv(&nat(0)),
            lam(bv(&nat(0)), lam(bool_ty(), record(&nat(0), triv()))),
        );
        let (a, b) = (0xffu64, 0x01u64);
        let v = fold(
            &arena,
            motive(2, 1, Some(())),
            base,
            add_step(),
            8,
            &[record(&nat(8), word(8, u128::from(a))), record(&nat(8), word(8, u128::from(b))), bit(false)],
        );
        assert_eq!(produced(&arena, v), (8, (a + b) & 0xff));
    }

    #[test]
    fn a_width_past_the_cap_is_a_second_run_over_the_first_tail() {
        // Design §13's answer to §3.4's widening worry: not a wider field,
        // but a run over a run. The outer word holds the cap; its tail is
        // the same fold at the residual width, which produces the rest.
        let arena = ValueArena::new();
        let base = lam(bv(&nat(0)), lam(bv(&nat(0)), record(&nat(0), triv())));
        let width = BIT_RUN_WIDTH_CAP + 3;
        let v = fold(
            &arena,
            motive(2, 0, Some(())),
            base,
            xor_step(),
            u64::from(width),
            &[
                record(&nat(u64::from(width)), word(width, 0)),
                record(&nat(u64::from(width)), word(width, (1u128 << width) - 1)),
            ],
        );
        let (held, bits) = produced(&arena, v);
        assert_eq!(held, BIT_RUN_WIDTH_CAP);
        assert_eq!(bits, u64::MAX);
    }

    #[test]
    fn a_scaled_consumer_reads_the_word_as_one_literal() {
        // `toNat` of a literal: Horner with a constant scale, so the whole
        // fold is one run and not one successor per bit.
        let arena = ValueArena::new();
        let base = lam(bv(&nat(0)), Rc::new(Term::Zero));
        let v = fold(
            &arena,
            motive(1, 0, None),
            base,
            to_nat_step(),
            8,
            &[record(&nat(8), word(8, 0b1011_0101))],
        );
        let Val::NatRun { program, .. } = &*v else { panic!("not a run: {v:?}") };
        assert!(matches!(&**program,
            ContextProgram::Run { count, .. } if count.get() == 0b1011_0101));
    }


    /// `is_zero_bits`' step: `not(head) && ih(tail)` — a **finite** output,
    /// short-circuiting at a set bit and reading the recursive result at a
    /// clear one (design §5).
    fn is_zero_step() -> Rc<Term> {
        // Scope in the body: x = 0, ih = 1, k = 2.
        let k = var(2);
        let xb = bits_of(&succ(&k), var(0));
        let call = app(var(1), bv(&k), record(&k, vtail(&k, Rc::clone(&xb))));
        let not_head = not_bit(vhead(&k, xb));
        // `and(a, b) = match a { False => False, True => b }`.
        let body = case(not_head, bool_ty(), bit(false), call);
        lam(bv(&succ(&var(1))), body)
    }

    /// A **pass** step: the bit drives nothing and the recursive result is
    /// handed back — `drop_low`'s shape, at a result width that does not
    /// depend on the fold's own.
    fn drop_step() -> Rc<Term> {
        let k = var(2);
        let xb = bits_of(&succ(&k), var(0));
        let body = app(var(1), bv(&k), record(&k, vtail(&k, xb)));
        lam(bv(&succ(&var(1))), body)
    }

    /// `λ n. BitVec(n) → R`, for a result that is not a vector at `n`.
    fn consumer_motive(result: Rc<Type>) -> Rc<Type> {
        Rc::new(Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: bv(&var(0)),
            cod: result,
        })
    }

    #[test]
    fn a_finite_consumer_is_a_table_over_the_bit_and_the_recursive_value() {
        let arena = ValueArena::new();
        let class = classify(&arena, consumer_motive(bool_ty()), is_zero_step())
            .expect("classified");
        assert_eq!(class.modes, vec![ArgMode::Peeled(0)]);
        let Output::Finite { values, table } = &class.output else { panic!("not finite") };
        assert_eq!(values.len(), 2);
        // `values[0]` is the left injection — `False` — so at a clear bit
        // the answer is the recursive one, and at a set bit it is `False`.
        assert_eq!(table, &vec![0, 1, 0, 0]);
        assert_eq!(class.run_finite(64, &[0], 0, 1), Some(1));
        assert_eq!(class.run_finite(64, &[1 << 40], 0, 1), Some(0));
    }

    #[test]
    fn a_finite_consumer_answers_a_whole_word_at_once() {
        let arena = ValueArena::new();
        let base = lam(bv(&nat(0)), bit(true));
        for (bits, expect) in [(0u128, true), (1u128 << 7, false), (1, false)] {
            let v = fold(
                &arena,
                consumer_motive(bool_ty()),
                Rc::clone(&base),
                is_zero_step(),
                8,
                &[record(&nat(8), word(8, bits))],
            );
            let got = match &*v {
                Val::Inl { .. } => false,
                Val::Inr { .. } => true,
                other => panic!("not a bit: {other:?}"),
            };
            assert_eq!(got, expect, "bits {bits:#x}");
        }
    }

    /// `case(ih(tx, ty)) { False => ih(ty, tx), True => True }`: the
    /// recursive result is read at the tails, and a **second** call at
    /// different arguments hides in a branch on it. A table over
    /// `(bit, ih(tails))` cannot express this fold, so the probe must
    /// decline it — which it does only because the branch is replayed with
    /// `ih` neutral and comes back stuck.
    fn hidden_second_call_step() -> Rc<Term> {
        // Scope in the body: y = 0, x = 1, ih = 2, k = 3.
        let k = var(3);
        let xb = bits_of(&succ(&k), var(1));
        let yb = bits_of(&succ(&k), var(0));
        let tx = record(&k, vtail(&k, xb));
        let ty = record(&k, vtail(&k, yb));
        let call = |a: &Rc<Term>, b: &Rc<Term>| {
            app(app(var(2), bv(&k), Rc::clone(a)), bv(&k), Rc::clone(b))
        };
        let body = case(call(&tx, &ty), bool_ty(), call(&ty, &tx), bit(true));
        lam(bv(&succ(&var(1))), lam(bv(&succ(&var(2))), body))
    }

    #[test]
    fn a_second_recursive_call_hidden_in_a_branch_declines() {
        let arena = ValueArena::new();
        let motive = Rc::new(Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: bv(&var(0)),
            cod: Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: bv(&var(1)),
                cod: bool_ty(),
            }),
        });
        assert!(classify(&arena, motive, hidden_second_call_step()).is_none());
    }

    #[test]
    fn a_pass_step_hands_back_the_fold_at_the_tail() {
        let arena = ValueArena::new();
        let class = classify(&arena, consumer_motive(bv(&nat(0))), drop_step())
            .expect("classified");
        assert!(matches!(class.output, Output::Pass));
        let base = lam(bv(&nat(0)), record(&nat(0), triv()));
        let v = fold(
            &arena,
            consumer_motive(bv(&nat(0))),
            base,
            drop_step(),
            8,
            &[record(&nat(8), word(8, 0xa5))],
        );
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, &arena);
        let inner = ev
            .slot_of(&[Proj::Snd, Proj::Fst], v)
            .expect("fuel")
            .expect("a record");
        assert!(matches!(&*inner, Val::Triv { .. }), "not the empty vector: {inner:?}");
    }

    // -- running the probe -------------------------------------------------

    fn classify<'v>(
        arena: &'v ValueArena<'v>,
        motive_ty: Rc<Type>,
        step: Rc<Term>,
    ) -> Option<Rc<Transducer>> {
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, arena);
        let m = arena.ty(TyClo::new(Env::empty(), motive_ty));
        let s = arena.tm(TmClo::syn(Env::empty(), step));
        ev.classify_transducer(s, m).expect("fuel")
    }

    #[test]
    fn xor_tabulates_to_four_entries_over_two_peeled_arguments() {
        // §11.4, the first half: `bxor` at width 2 by hand.
        let arena = ValueArena::new();
        let class = classify(&arena, motive(2, 0, Some(())), xor_step()).expect("classified");
        assert_eq!(class.modes, vec![ArgMode::Peeled(0), ArgMode::Peeled(1)]);
        assert_eq!(class.peeled, 2);
        assert_eq!(class.states.len(), 1);
        assert_eq!(class.combinations(), 4);
        // The recursive arguments were projection-path recognizable: the
        // class exists at all only if every combination's `ih` was found at
        // the probe's own tails, inside the record's wrapper.
        assert_eq!(class.slots, vec![vec![Proj::Snd, Proj::Fst], vec![Proj::Snd, Proj::Fst]]);
        assert_eq!(class.out_slot, vec![Proj::Snd, Proj::Fst]);
        let Output::Cons { bits } = &class.output else { panic!("not a cons output") };
        assert_eq!(bits, &vec![false, true, true, false]);
        assert_eq!(class.next, vec![0; 4]);
        // And the machine is exclusive-or at the full width.
        let (word, _) = class.run_cons(64, &[0xdead_beef, 0x0123_4567], 0).unwrap();
        assert_eq!(word, 0xdead_beef ^ 0x0123_4567);
    }

    #[test]
    fn a_carry_reaches_the_recursive_call_closed_and_tabulates_to_eight() {
        // §11.4, the second half: the `match carry` before the recursive
        // call reduces at a closed carry, so the probe sees
        // `ih(t_a, t_b, closed)` and not a stuck case split.
        let arena = ValueArena::new();
        let class = classify(&arena, motive(2, 1, Some(())), add_step()).expect("classified");
        assert_eq!(
            class.modes,
            vec![ArgMode::Peeled(0), ArgMode::Peeled(1), ArgMode::State(0)]
        );
        assert_eq!(class.states.len(), 2);
        assert_eq!(class.combinations(), 8);
        let Output::Cons { .. } = &class.output else { panic!("not a cons output") };
        let (x, y) = (0x0123_4567_89ab_cdefu64, 0xfedc_ba98_7654_3210u64);
        let (sum, carry) = class.run_cons(64, &[x, y], 0).unwrap();
        assert_eq!(sum, x.wrapping_add(y));
        assert_eq!(carry, u32::from(x.checked_add(y).is_none()));
        // With the carry in: one more.
        let (sum, _) = class.run_cons(64, &[x, y], 1).unwrap();
        assert_eq!(sum, x.wrapping_add(y).wrapping_add(1));
    }

    #[test]
    fn an_open_index_stays_opaque() {
        // §11.5, the negative control: `set` is not refused, it is simply
        // not accelerated.
        let arena = ValueArena::new();
        assert!(classify(&arena, motive(1, 0, Some(())), set_step()).is_none());
    }

    #[test]
    fn to_nat_is_a_scaled_leaf_and_not_an_affine_tree() {
        // §11.6: the `Nat` classes report `Opaque` — the step returns a
        // function — and the consumer mode is what changes it. The scale is
        // two at every bit, which is what makes the whole word one literal.
        let arena = ValueArena::new();
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, &arena);
        let step = arena.tm(TmClo::syn(Env::empty(), to_nat_step()));
        assert!(matches!(&*ev.classify_step(step).expect("fuel"), FoldClass::Opaque));

        let class = classify(&arena, motive(1, 0, None), to_nat_step()).expect("classified");
        assert_eq!(class.modes, vec![ArgMode::Peeled(0)]);
        let Output::Scaled { maps } = &class.output else { panic!("not a scaled output") };
        assert_eq!(maps.len(), 2);
        for (q, _) in maps {
            assert!(matches!(q.as_deref(),
                Some(ContextProgram::Run { count, .. }) if count.get() == 2));
        }
        // `r` is the bit's own value: zero, then one.
        assert!(maps[0].1.is_none());
        assert!(matches!(maps[1].1.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 1));
        // Horner over a word is the word: `toNat` of a literal is a literal.
        let (q, r) = class.run_scaled(8, &[0b1011_0101], 0).unwrap();
        assert!(matches!(q.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 256));
        assert!(matches!(r.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 0b1011_0101));
    }
}
