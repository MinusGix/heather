(* Heather's Wf as a Rocq inductive with the positivity and guard checks
   bypassed (docs/library/export-fragment-design.md §5.1): β at an open tag holds, and
   the property Wf exists for holds only eta-long, since Rocq has no unit eta.
   Print Assumptions names both bypasses. *)
Set Universe Polymorphism.
Set Primitive Projections.
Unset Universe Minimization ToSet.

Record Sig@{u v} {A : Type@{u}} (B : A -> Type@{v}) : Type@{max(u,v)} := pair { fst : A; snd : B fst }.
Arguments pair {A B} fst snd. Arguments fst {A B} s. Arguments snd {A B} s.
Inductive Empty@{u} : Type@{u} := .
Inductive Unit@{u} : Type@{u} := tt.
Inductive Sum@{u v} (A : Type@{u}) (B : Type@{v}) : Type@{max(u,v)} := inl (a : A) | inr (b : B).
Arguments inl {A B} a. Arguments inr {A B} b.

Fixpoint Vec@{u} (A : Type@{u}) (n : nat) : Type@{u} :=
  match n with O => Unit@{u} | S k => Sig@{u u} (fun _ : A => Vec A k) end.
Fixpoint Fin (n : nat) : Type@{Set} :=
  match n with O => Empty@{Set} | S k => Sum@{Set Set} Unit@{Set} (Fin k) end.
Fixpoint nth@{u} {A : Type@{u}} (n : nat) : Vec A n -> Fin n -> A :=
  match n with
  | O => fun _ i => match i with end
  | S k => fun v i => match i with inl _ => fst v | inr j => nth k (snd v) j end
  end.

#[bypass_check(positivity)]
Inductive Wf@{u} (S : Type@{u}) (n : S -> nat) : Type@{u} :=
  supf (a : S) (cs : Vec@{u} (Wf S n) (n a)).
Arguments supf {S n} a cs.

#[bypass_check(guard)]
Fixpoint elimWf@{u v} {S : Type@{u}} {n : S -> nat} (M : Wf S n -> Type@{v})
  (step : forall (a : S) (cs : Vec (Wf S n) (n a)),
          (forall i : Fin (n a), M (nth (n a) cs i)) -> M (supf a cs))
  (t : Wf S n) {struct t} : M t :=
  match t with supf a cs => step a cs (fun i => elimWf M step (nth (n a) cs i)) end.

(* beta at a NEUTRAL tag: exact *)
Check (fun S n M step (a : S) cs =>
  (eq_refl : @elimWf S n M step (supf a cs) = step a cs (fun i => elimWf M step (nth (n a) cs i)))).
(* the property Wf exists for: abstract children at canonical arity == concrete node *)
Definition W2 := Wf nat (fun _ => 2).
(* without eta-long: needs unit eta at the tail *)
Fail Check (fun (cs : Vec W2 2) =>
  (eq_refl : @supf nat (fun _ => 2) 0 cs = @supf nat (fun _ => 2) 0 (pair (nth 2 cs (inl tt)) (pair (nth 2 cs (inr (inl tt))) tt)))).
(* eta-long translation of the neutral cs at its canonical type *)
Check (fun (cs : Vec W2 2) =>
  (eq_refl : @supf nat (fun _ => 2) 0 (pair (fst cs) (pair (fst (snd cs)) tt)) = @supf nat (fun _ => 2) 0 (pair (nth 2 cs (inl tt)) (pair (nth 2 cs (inr (inl tt))) tt)))).
Print Assumptions elimWf.
