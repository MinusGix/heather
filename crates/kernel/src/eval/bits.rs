//! The bit criterion, and packing a `Vec` prefix into a machine word
//! (`docs/native-bitvector-values-design.md` §§3.1, 7).
//!
//! `Vec^l(T; n)` is a right-nested Σ (`docs/wf-former-design.md` §1.2), so a
//! vector of `n` elements is `n` pair nodes. When `T` has exactly **two**
//! canonical inhabitants and both payloads are proof-irrelevant — which is
//! precisely what a two-constructor nullary inductive lowers to
//! (`docs/inductive-tier0-lowering.md` §3: `Tag_D`-prefixed field spines
//! under a sum) — the whole chain is `n` bits, and everything a consumer can
//! observe about element `i` is which injection it is.
//!
//! Nothing here reads a definition's spelling. The criterion is a fact about
//! the *type*, decided by forcing it, and memoized on the element closure in
//! the value arena beside the fold classes. The canonical inhabitants of the
//! two halves are built once, when the criterion is decided, because
//! unpacking a run has to reproduce the element type's own injections and
//! the consumers that unpack have no evaluator in hand (design §13).
//!
//! Packing is **on demand and type-directed** (design §3.2): it happens where
//! the type is in hand and the walk is one the caller was going to perform
//! anyway — conversion's Σ-η arm. It never δ-unfolds a chain's spine, so a
//! neutral side is left to the comparison that decides neutrals on their
//! spines; it does force the *element*, which is what comparing two bits at a
//! sum type needs regardless.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::value::{
    BitTy, Elim, SigAnn, SumAnn, TmClo, TyClo, VTy, Val, BIT_RUN_WIDTH_CAP,
};

use super::{Eval, Res};

/// How deep a unit-like Σ-nest, or a canonical payload, may be.
///
/// `Tag_D` is the binary representation of a declaration id, so the nest is
/// `O(log id_D)` deep and this is slack of several orders. The bound exists
/// so that neither the criterion nor the payload check can recurse on the
/// native stack over an adversarial type.
pub(crate) const UNIT_NEST_LIMIT: u32 = 64;

/// A common prefix of two vectors, read as two machine words
/// (design §7): at least one bit was consumed from each side, and
/// `left`/`right` are what is left, at the type `ty`.
pub(crate) struct BitPrefix<'v> {
    pub left_bits: u64,
    pub right_bits: u64,
    pub left: Rc<Val<'v>>,
    pub right: Rc<Val<'v>>,
    /// The `Vec` at the residual length — the type the two residuals are
    /// compared at, taken from the type walk and not reconstructed.
    pub ty: &'v TyClo<'v>,
}

/// One node of the `Vec`'s Σ-chain: the annotations a projection out of it
/// carries. A `Vec`'s Σ has one level on both sides and a tail that does not
/// mention the binder, which is what lets the same record travel down the
/// chain as an ordinary value.
struct Sigma<'v> {
    level: Level,
    fst: &'v TyClo<'v>,
    snd: &'v TyClo<'v>,
}

impl<'v> Sigma<'v> {
    fn proj(&self, first: bool) -> Elim<'v> {
        let (fst_level, snd_level) = (self.level.clone(), self.level.clone());
        let (fst_ty, snd_ty) = (self.fst, self.snd);
        let ann = Some(SigAnn { fst_level, snd_level, fst_ty, snd_ty });
        if first { Elim::Fst { ann } } else { Elim::Snd { ann } }
    }
}

impl<'v> Eval<'_, 'v> {
    /// Whether `elem` is a *bit type*, and with what injections. Decided
    /// once per element closure and memoized in the arena; the negative
    /// verdict is memoized too, since it is the common one.
    pub(crate) fn bit_ty(&mut self, elem: &'v TyClo<'v>) -> Res<Option<&'v BitTy<'v>>> {
        if let Some(found) = self.arena.bit_type(elem) {
            return Ok(found);
        }
        let decided = self.decide_bit_ty(elem)?;
        self.arena.cache_bit_type(elem, decided);
        Ok(decided)
    }

    fn decide_bit_ty(&mut self, elem: &'v TyClo<'v>) -> Res<Option<&'v BitTy<'v>>> {
        // δ-transparently: an element type reached through the elaborator is
        // an `El` of a *glued* code, and the criterion is a question about
        // the type, decided once and memoized — not a term comparison whose
        // δ discipline this could disturb.
        let w = self.force_ty(elem)?;
        let w = self.delta_whnf_ty(w)?;
        let VTy::Sum { lhs_level, rhs_level, lhs, rhs } = &*w else {
            return Ok(None);
        };
        let (lhs_level, rhs_level, lhs, rhs) =
            (lhs_level.clone(), rhs_level.clone(), *lhs, *rhs);
        let (Some(zero), Some(one)) = (
            self.unit_inhabitant(lhs, UNIT_NEST_LIMIT)?,
            self.unit_inhabitant(rhs, UNIT_NEST_LIMIT)?,
        ) else {
            return Ok(None);
        };
        let zero = self.vclo(Rc::new(Val::Inl {
            ann: Some(SumAnn {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs,
                rhs,
            }),
            val: zero,
        }));
        let one = self.vclo(Rc::new(Val::Inr {
            ann: Some(SumAnn { lhs_level, rhs_level, lhs, rhs }),
            val: one,
        }));
        Ok(Some(self.arena.bit_ty(BitTy { elem, zero, one })))
    }

    /// The canonical inhabitant of a *unit-like* type — `Unit`, a strict
    /// equality (whose canonical proof is `srefl` at its left endpoint: the
    /// nominal tag a declared inductive's constructors carry), or a Σ-nest of
    /// those — and `None` for anything else. The Σ's tail is
    /// instantiated at the first component's own inhabitant, which is what
    /// makes the reading total for a dependent nest as well as a constant
    /// one; the pair keeps the **uninstantiated** tail as its annotation,
    /// which is where a pair's `snd_ty` is scoped.
    pub(crate) fn unit_inhabitant(
        &mut self,
        ty: &'v TyClo<'v>,
        depth: u32,
    ) -> Res<Option<&'v TmClo<'v>>> {
        if depth == 0 {
            return Ok(None);
        }
        let w = self.force_ty(ty)?;
        let w = self.delta_whnf_ty(w)?;
        match &*w {
            VTy::Unit { level } => {
                let level = level.clone();
                Ok(Some(self.vclo(Rc::new(Val::Triv { level }))))
            }
            VTy::SEq { level, ty, lhs, rhs } => {
                let (level, ty, tm, rhs) = (level.clone(), *ty, *lhs, *rhs);
                if !self.seq_is_unit(tm, rhs)? {
                    return Ok(None);
                }
                Ok(Some(self.vclo(Rc::new(Val::SRefl { level, ty, tm }))))
            }
            VTy::Sigma { fst_level, snd_level, fst, snd } => {
                let (fst_level, snd_level, fst, snd) =
                    (fst_level.clone(), snd_level.clone(), *fst, *snd);
                let Some(head) = self.unit_inhabitant(fst, depth - 1)? else {
                    return Ok(None);
                };
                let rest_ty = self.apply_ty(snd, &[head])?;
                let rest_ty = self.arena.ty(TyClo::val(rest_ty));
                let Some(rest) = self.unit_inhabitant(rest_ty, depth - 1)? else {
                    return Ok(None);
                };
                Ok(Some(self.vclo(Rc::new(Val::Pair {
                    ann: Some(SigAnn {
                        fst_level,
                        snd_level,
                        fst_ty: fst,
                        snd_ty: snd,
                    }),
                    fst: head,
                    snd: rest,
                }))))
            }
            _ => Ok(None),
        }
    }

    /// Whether a strict equality `sEq(I; lhs; rhs)` is unit-like: both
    /// endpoints the **same closed natural number**, which is the nominal
    /// tag's shape (`docs/inductive-tier0-lowering.md` §3.3). Then `srefl` is
    /// its one inhabitant up to conversion. An `sEq` at unequal endpoints is
    /// *empty*, and one at open or non-`Nat` endpoints is not decided here
    /// (that would be conversion's job), so both answer `false` and the type
    /// is simply not unit-like — never a guess.
    pub(crate) fn seq_is_unit(&mut self, lhs: &'v TmClo<'v>, rhs: &'v TmClo<'v>) -> Res<bool> {
        let (Some(a), Some(b)) = (self.closed_nat(lhs)?, self.closed_nat(rhs)?) else {
            return Ok(false);
        };
        Ok(a == b)
    }

    /// A closed natural number's value, when it is one and fits a `u64`:
    /// `Zero`, successors and saturated runs, walked through their tails.
    /// `None` for anything open, stuck or larger.
    fn closed_nat(&mut self, c: &'v TmClo<'v>) -> Res<Option<u64>> {
        let mut total = 0u64;
        let mut v = self.force(c)?;
        loop {
            let next = match &*v {
                Val::Zero => return Ok(Some(total)),
                Val::Succ(pred) => {
                    let Some(t) = total.checked_add(1) else { return Ok(None) };
                    total = t;
                    *pred
                }
                Val::NatRun { program, tail } => {
                    let Some(n) = crate::value::program::ContextProgram::repetition_count_up_to(
                        program,
                        u64::MAX - total,
                    ) else {
                        return Ok(None);
                    };
                    total += n;
                    *tail
                }
                _ => return Ok(None),
            };
            v = self.force(next)?;
        }
    }

    /// The bit a *bit value* stands for: `Inl`/`Inr` over the canonical
    /// inhabitant of its half. Requiring the payload to be canonical is what
    /// makes unpacking reproduce the same value rather than a merely
    /// convertible one (design §3.1); anything else does not pack and stays
    /// structural.
    pub(crate) fn bit_of(&mut self, v: &Rc<Val<'v>>) -> Res<Option<bool>> {
        let (bit, payload) = match &**v {
            Val::Inl { val, .. } => (false, *val),
            Val::Inr { val, .. } => (true, *val),
            _ => return Ok(None),
        };
        Ok(if self.is_canonical_unit(payload, UNIT_NEST_LIMIT)? {
            Some(bit)
        } else {
            None
        })
    }

    pub(crate) fn is_canonical_unit(&mut self, c: &'v TmClo<'v>, depth: u32) -> Res<bool> {
        if depth == 0 {
            return Ok(false);
        }
        let v = self.force(c)?;
        Ok(match &*v {
            // `srefl`'s endpoint is not an observation: well-typedness fixes
            // it up to conversion, every consumer of a strict-equality proof
            // is `transp`, whose β ignores it, and conversion at `sEq` is
            // irrelevant.
            Val::Triv { .. } | Val::SRefl { .. } => true,
            Val::Pair { fst, snd, .. } => {
                self.is_canonical_unit(fst, depth - 1)?
                    && self.is_canonical_unit(snd, depth - 1)?
            }
            _ => false,
        })
    }

    /// One bit off the head of a vector value, with what is left of it.
    ///
    /// Three shapes, and the third is the point (design §7, "native against
    /// structural"): a `Pair` reads its own fields, a run gives its first bit
    /// through [`Val::bit_run_unpack`] — the same Σ-chain every other
    /// consumer sees — and **anything else is projected**, with the Σ's own
    /// annotations, which is exactly the `fst`/`snd` the η arm was about to
    /// perform and in the same order. A computed vector is a stuck
    /// projection until its definition unfolds, so the head is taken
    /// δ-transparently; that is the same unfolding comparing this bit
    /// against a canonical one at the sum type would force anyway.
    fn bit_step(
        &mut self,
        bt: &'v BitTy<'v>,
        sigma: &Sigma<'v>,
        v: &Rc<Val<'v>>,
    ) -> Res<Option<(bool, Rc<Val<'v>>)>> {
        let (head, rest) = match &**v {
            Val::Pair { fst, snd, .. } => (self.force(fst)?, self.force(snd)?),
            Val::BitRun { level, ty, width, bits, tail_len, tail } => {
                if !std::ptr::eq(ty.elem, bt.elem) {
                    return Ok(None);
                }
                let pair = Val::bit_run_unpack(
                    self.arena, level, ty, *width, *bits, tail_len, tail,
                );
                let Val::Pair { fst, snd, .. } = pair else {
                    unreachable!("a run unpacks to a pair")
                };
                (self.force(fst)?, self.force(snd)?)
            }
            _ => {
                let head = self.elim(Rc::clone(v), sigma.proj(true))?;
                let rest = self.elim(Rc::clone(v), sigma.proj(false))?;
                (head, rest)
            }
        };
        let head = self.delta_whnf(head)?;
        Ok(self.bit_of(&head)?.map(|bit| (bit, rest)))
    }

    /// Pack the longest common prefix of two vectors at `tail_ty`'s Σ-chain
    /// into two words (design §7). `None` is "not one bit packed", which
    /// leaves the caller's behaviour exactly as it is today.
    ///
    /// The value walk and the type walk go in lockstep: `tail_ty` is the Σ's
    /// own tail, so each further bit costs one [`Eval::vec_ty`] — which is
    /// what η would have paid for the *type* anyway — and the residual type
    /// is the one the walk stopped at, never a reconstructed length.
    pub(crate) fn pack_bit_prefix(
        &mut self,
        level: &Level,
        elem: &'v TyClo<'v>,
        tail_ty: &'v TyClo<'v>,
        mut left: Rc<Val<'v>>,
        mut right: Rc<Val<'v>>,
    ) -> Res<Option<BitPrefix<'v>>> {
        let Some(bt) = self.bit_ty(elem)? else { return Ok(None) };
        let (mut left_bits, mut right_bits) = (0u64, 0u64);
        let mut width = 0u32;
        // The type of the values one bit further in; `out_ty` is recorded
        // *before* the step, so a chain that stops being a Σ still hands
        // back its residuals at the type it stopped at.
        let mut sigma = Sigma { level: level.clone(), fst: elem, snd: tail_ty };
        let mut out_ty = tail_ty;
        while width < BIT_RUN_WIDTH_CAP {
            let Some((l_bit, l_rest)) = self.bit_step(bt, &sigma, &left)? else { break };
            let Some((r_bit, r_rest)) = self.bit_step(bt, &sigma, &right)? else { break };
            // One fuel unit per bit consumed (design §8): strictly less than
            // the η path spent on the same bit, so no verdict fuel allowed
            // today becomes a refusal.
            self.spend()?;
            left_bits |= u64::from(l_bit) << width;
            right_bits |= u64::from(r_bit) << width;
            width += 1;
            left = l_rest;
            right = r_rest;
            out_ty = sigma.snd;
            // Two canonical bits that differ settle the comparison: the
            // element type has exactly two inhabitants and they are
            // different injections, so no residual can rescue the pair.
            // Stopping here is what makes a difference at bit 0 cost one
            // projection and not a whole word's worth (design §8).
            if l_bit != r_bit {
                break;
            }
            let w = self.force_ty(sigma.snd)?;
            let VTy::Sigma { fst, snd, .. } = &*w else { break };
            // The next component is a bit only if it is at the same element
            // type; a `Vec`'s chain always is, and nothing else continues.
            if !std::ptr::eq(*fst, elem) {
                break;
            }
            sigma = Sigma { level: sigma.level, fst: *fst, snd: *snd };
        }
        if width == 0 {
            return Ok(None);
        }
        Ok(Some(BitPrefix { left_bits, right_bits, left, right, ty: out_ty }))
    }

    /// A run over a closed tail, for the tests and for round 3's merging
    /// frame: `bits` of `width` over `Triv`, at `elem`'s injections.
    #[cfg(test)]
    pub(crate) fn closed_bit_run(
        &mut self,
        level: &Level,
        elem: &'v TyClo<'v>,
        width: u32,
        bits: u64,
    ) -> Res<Option<Val<'v>>> {
        let Some(ty) = self.bit_ty(elem)? else { return Ok(None) };
        let tail_len = self.vclo(Rc::new(Val::Zero));
        let tail = self.vclo(Rc::new(Val::Triv { level: level.clone() }));
        Ok(Some(Val::BitRun {
            level: level.clone(),
            ty,
            width,
            bits,
            tail_len,
            tail,
        }))
    }
}

#[cfg(test)]
mod tests {
    //! The round trips design §8 asks for, seed-only in the `law!` spirit:
    //! a failing case is reported by its seed, because a disagreeing word is
    //! exactly the value that would fill a log.

    use super::*;
    use crate::reduce::Defs;
    use crate::term::{CtxBase, Type};
    use crate::value::{Env, ValueArena, BIT_RUN_WIDTH_CAP};

    const FUEL: u64 = 1_000_000;

    /// `Unit + Unit`: the smallest type that meets the criterion.
    fn elem_ty<'v>(arena: &'v ValueArena<'v>) -> &'v TyClo<'v> {
        let unit = || Rc::new(Type::Unit { level: Level::Zero });
        arena.ty(TyClo::new(
            Env::empty(),
            Rc::new(Type::Sum {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: unit(),
                rhs: unit(),
            }),
        ))
    }

    fn lcg(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *seed >> 33
    }

    #[test]
    fn unpacking_a_run_one_bit_at_a_time_reads_back_the_word() {
        let arena = ValueArena::new();
        let mut seed = 21;
        for case in 0..64u64 {
            let width = (lcg(&mut seed) % u64::from(BIT_RUN_WIDTH_CAP)) as u32 + 1;
            let bits = lcg(&mut seed) & mask(width);
            let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, &arena);
            let elem = elem_ty(&arena);
            let run = ev
                .closed_bit_run(&Level::Zero, elem, width, bits)
                .expect("fuel")
                .expect("the criterion holds");
            // Walk the Σ-chain the run stands for, one `Pair` at a time.
            let mut read = 0u64;
            let mut cur = Rc::new(run);
            for i in 0..width {
                let Val::BitRun { level, ty, width: w, bits: b, tail_len, tail } = &*cur else {
                    panic!("seed {case}: chain ended at bit {i}");
                };
                let pair =
                    Val::bit_run_unpack(&arena, level, ty, *w, *b, tail_len, tail);
                let Val::Pair { fst, snd, .. } = pair else { unreachable!() };
                let head = ev.force(fst).expect("fuel");
                let bit = ev.bit_of(&head).expect("fuel").expect("a bit value");
                read |= u64::from(bit) << i;
                cur = ev.force(snd).expect("fuel");
            }
            assert_eq!(read, bits, "seed {case}");
            assert!(matches!(&*cur, Val::Triv { .. }), "seed {case}: tail is not ⟨⟩");
        }
    }

    #[test]
    fn packing_two_runs_reads_both_words_and_stops_at_the_first_difference() {
        let arena = ValueArena::new();
        let mut seed = 33;
        for case in 0..64u64 {
            let width = (lcg(&mut seed) % u64::from(BIT_RUN_WIDTH_CAP)) as u32 + 1;
            let a = lcg(&mut seed) & mask(width);
            let b = lcg(&mut seed) & mask(width);
            let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, &arena);
            let elem = elem_ty(&arena);
            let left = ev.closed_bit_run(&Level::Zero, elem, width, a).unwrap().unwrap();
            let right = ev.closed_bit_run(&Level::Zero, elem, width, b).unwrap().unwrap();
            // The Σ-tail of the *first* pair: a `Vec` at one less than the
            // words' width, which is the type `pack_bit_prefix` walks in
            // lockstep with the values.
            let mut len = ev.vclo(Rc::new(Val::Zero));
            for _ in 1..width {
                len = ev.vclo(Rc::new(Val::Succ(len)));
            }
            let tail_ty = arena.ty_vec(Level::Zero, elem, len);
            let prefix = ev
                .pack_bit_prefix(&Level::Zero, elem, tail_ty, Rc::new(left), Rc::new(right))
                .expect("fuel");
            let prefix = prefix.expect("at least one bit packs");
            let differ = a ^ b;
            if differ == 0 {
                assert_eq!(prefix.left_bits, a, "seed {case}");
                assert_eq!(prefix.right_bits, b, "seed {case}");
            } else {
                // The walk stops one bit past the first difference, so the
                // words differ — which is the verdict — and no more bits
                // than that were ever projected.
                assert_ne!(prefix.left_bits, prefix.right_bits, "seed {case}");
                let taken = 64 - prefix.left_bits.leading_zeros().min(63);
                assert!(taken <= differ.trailing_zeros() + 1, "seed {case}");
            }
        }
    }

    /// What a declared two-constructor nullary inductive lowers to: each half
    /// is its nominal tag `sEq⁰(Nat; k; k)` followed by the `Unit` terminator
    /// (`docs/inductive-tier0-lowering.md` §3.3). The tag's proof is part of
    /// the canonical payload, so the criterion must read `srefl` as unit-like
    /// or no declared enum would ever pack.
    #[test]
    fn a_strictly_tagged_two_constructor_type_meets_the_criterion() {
        use crate::term::Term;
        let arena = ValueArena::new();
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, &arena);
        let half = || {
            let k = Rc::new(Term::NatLit(5));
            Rc::new(Type::Sigma {
                fst_level: Level::Zero,
                snd_level: Level::Zero,
                fst: Rc::new(Type::SEq {
                    level: Level::Zero,
                    ty: Rc::new(Type::Nat),
                    lhs: Rc::clone(&k),
                    rhs: k,
                }),
                snd: Rc::new(Type::Unit { level: Level::Zero }),
            })
        };
        let elem = arena.ty(TyClo::new(
            Env::empty(),
            Rc::new(Type::Sum {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: half(),
                rhs: half(),
            }),
        ));
        for bits in [0b0110u64, 0b1001] {
            let Some(Val::BitRun { level, ty, width, bits: b, tail_len, tail }) =
                ev.closed_bit_run(&Level::Zero, elem, 4, bits).expect("fuel")
            else {
                panic!("a strictly tagged enum meets the criterion")
            };
            let pair = Val::bit_run_unpack(&arena, &level, ty, width, b, tail_len, tail);
            let Val::Pair { fst, .. } = pair else { unreachable!() };
            let head = ev.force(fst).expect("fuel");
            assert_eq!(ev.bit_of(&head).expect("fuel"), Some(bits & 1 == 1));
        }
    }

    #[test]
    fn a_word_over_wide_by_one_keeps_its_last_bit_in_the_tail() {
        // The cap is a *representation* bound, not a semantic one: the bit
        // past it is the residual's, and it must still be there.
        let arena = ValueArena::new();
        let mut ev = Eval::new(FUEL, Defs::opaque(), CtxBase::Nil, &arena);
        let elem = elem_ty(&arena);
        assert!(ev
            .closed_bit_run(&Level::Zero, elem, BIT_RUN_WIDTH_CAP, u64::MAX)
            .unwrap()
            .is_some());
        // One more bit does not fit: `bit_run_cons` refuses at the cap, and
        // the caller keeps a structural pair over the run.
        let Some(Val::BitRun { ty, width, bits, tail_len, tail, .. }) = ev
            .closed_bit_run(&Level::Zero, elem, BIT_RUN_WIDTH_CAP, 0)
            .unwrap()
        else {
            panic!("the criterion holds")
        };
        assert!(
            Val::bit_run_cons(&Level::Zero, ty, true, width, bits, tail_len, tail).is_none()
        );
        // Below the cap it fits, and the new bit is the head.
        let Some(Val::BitRun { bits, width, .. }) = ev
            .closed_bit_run(&Level::Zero, elem, BIT_RUN_WIDTH_CAP - 1, 0)
            .unwrap()
            .and_then(|v| {
                let Val::BitRun { ty, width, bits, tail_len, tail, .. } = v else {
                    unreachable!()
                };
                Val::bit_run_cons(&Level::Zero, ty, true, width, bits, tail_len, tail)
            })
        else {
            panic!("one more bit fits below the cap")
        };
        assert_eq!(width, BIT_RUN_WIDTH_CAP);
        assert_eq!(bits & 1, 1);
    }

    fn mask(width: u32) -> u64 {
        if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        }
    }
}
