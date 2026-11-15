/- The per-declaration realisation of a tier-1 `Wf` instance as a native Lean
   inductive (docs/library/export-fragment-design.md §5.2), for `List<A>`. (1) and (2)
   check: the property `Wf` exists for, and β at a canonical tag. (3) does
   not: β at an *open* tag, which Heather has and this realisation lacks. -/
import Hx

noncomputable section
universe u
-- A Heather tier-1 List<A>: shape S = Sum (Σ(tag₀). Unit) (Σ(tag₁). Σ(A). Unit), arity 0 | 1.
variable (A : Type)
abbrev S := Hx.Sum (Hx.Sig (Hx.SEq Hx.Nat 0 0) (fun _ => Hx.Unit.{0}))
                    (Hx.Sig (Hx.SEq Hx.Nat 1 1) (fun _ => Hx.Sig A (fun _ => Hx.Unit.{0})))
abbrev n : S A → Hx.Nat := fun a => Hx.case _ _ (fun _ => Hx.Nat) (fun _ => 0) (fun _ => 1) a

-- The native realisation, one constructor per summand, children as fields.
inductive L
  | nil (p : Hx.Sig (Hx.SEq Hx.Nat 0 0) (fun _ => Hx.Unit.{0}))
  | cons (p : Hx.Sig (Hx.SEq Hx.Nat 1 1) (fun _ => Hx.Sig A (fun _ => Hx.Unit.{0}))) (x : L)

abbrev supf (a : S A) (cs : Hx.Vec (L A) (n A a)) : L A :=
  @Hx.Sum.rec _ _ (fun a => Hx.Vec (L A) (n A a) → L A) (fun p _ => L.nil p) (fun p cs => L.cons p cs.1) a cs

-- nth exactly as the kernel's schema shape (Nat recursion on the length, case on the index)
abbrev nth (k : Hx.Nat) : Hx.Vec (L A) k → Hx.Fin k → L A :=
  @Nat.rec (fun k => Hx.Vec (L A) k → Hx.Fin k → L A) (fun _ i => Hx.elimEmpty (fun _ => L A) i)
    (fun _ r cs i => Hx.case _ _ (fun _ => L A) (fun _ => cs.1) (fun j => r cs.2 j) i) k

abbrev elimWf (M : L A → Type) (step : (a : S A) → (cs : Hx.Vec (L A) (n A a)) →
      ((i : Hx.Fin (n A a)) → M (nth A (n A a) cs i)) → M (supf A a cs)) (t : L A) : M t :=
  @L.rec A M (fun p => step (Hx.Sum.inl p) Hx.tt (fun i => Hx.elimEmpty (fun i => M (nth A 0 Hx.tt i)) i))
    (fun p x ih => step (Hx.Sum.inr p) ⟨x, Hx.tt⟩
       (fun i => Hx.case _ _ (fun i => M (nth A 1 ⟨x, Hx.tt⟩ i)) (fun _ => ih) (fun j => Hx.elimEmpty (fun j => M (nth A 1 ⟨x, Hx.tt⟩ (Hx.inr _ _ j))) j) i)) t

-- (1) the property Wf exists for: abstract children at a canonical tag = concrete node
example (p) (cs : Hx.Vec (L A) 1) :
    supf A (Hx.Sum.inr p) cs = supf A (Hx.Sum.inr p) ⟨nth A 1 cs (Hx.Sum.inl Hx.tt), Hx.tt⟩ := rfl
-- (2) beta at a canonical tag, ih applied at a literal index
example (M : L A → Type) (step) (p) (cs : Hx.Vec (L A) 1) :
    elimWf A M step (supf A (Hx.Sum.inr p) cs) =
    step (Hx.Sum.inr p) cs (fun i => Hx.case _ _ (fun i => M (nth A 1 cs i)) (fun _ => elimWf A M step cs.1) (fun j => Hx.elimEmpty (fun j => M (nth A 1 cs (Hx.inr _ _ j))) j) i) := by
  with_unfolding_all rfl
-- (3) beta at an OPEN tag: Heather fires, this realisation is stuck
#guard_msgs (drop error) in
example (M : L A → Type) (step) (a : S A) (cs) :
    elimWf A M step (supf A a cs) = step a cs (fun i => elimWf A M step (nth A (n A a) cs i)) := rfl
