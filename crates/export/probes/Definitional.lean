/- Which of Heather's definitional rules Lean's kernel has, over prelude/Hx.lean
   (docs/export-fragment-design.md §3). Every `example` here checks; the
   `#guard_msgs (drop error)` ones are the rules Lean lacks, kept so a change
   in either system shows up. Run: scripts/export-recheck builds Hx.olean,
   then `LEAN_PATH=<that dir> lean Definitional.lean`. -/
import Hx
noncomputable section

-- sEq irrelevance: holds against a constructor, so eta-long proofs compare…
example (A : Type) (a b : A) (p q : Hx.SEq A a b) : (⟨p.pf⟩ : Hx.SEq A a b) = ⟨q.pf⟩ := rfl
-- …but two neutral proofs do not: structure eta needs a constructor side.
#guard_msgs (drop error) in
example (A : Type) (a b : A) (p q : Hx.SEq A a b) : p = q := rfl

-- Unit eta (unit-like structures, both sides neutral) and Σ eta.
example (x y : Hx.Unit.{0}) : x = y := rfl
example (A : Type) (B : A → Type) (p : Hx.Sig A B) : p = ⟨p.1, p.2⟩ := rfl

-- A tier-0 enum payload `Σ(_ : sEq(tag; tag)). Unit`: a neutral equals the
-- canonical payload, which is what `B::not_not` needs.
example (x : Hx.Sig (Hx.SEq Hx.Nat 0 0) (fun _ => Hx.Unit.{0})) :
    x = Hx.pair _ _ (Hx.srefl Hx.Nat 0) Hx.tt := rfl

-- Id is proof-relevant: no K.
#guard_msgs (drop error) in
example (A : Type) (a : A) (p : Hx.Id A a a) : p = Hx.refl A a := rfl
