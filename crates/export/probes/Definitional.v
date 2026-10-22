(* Which of Heather's definitional rules Rocq/Coq's kernel has, over
   prelude/Hx.v (docs/export-fragment-design.md §3). The `Fail` lines are the
   rules it lacks. *)
Require Import Hx.

(* sEq irrelevance against a constructor; not between neutrals. *)
Check (fun (A : Type) (a b : A) (p q : Hx.SEq A a b) =>
  (eq_refl : Hx.mkSEq (Hx.pf p) = Hx.mkSEq (Hx.pf q))).
Fail Check (fun (A : Type) (a b : A) (p q : Hx.SEq A a b) => (eq_refl : p = q)).
(* No unit eta at all, and no eta for the SEq record (it cannot be
   primitive), so a neutral enum payload is not the canonical one. *)
Fail Check (fun (x y : Hx.Unit) => (eq_refl : x = y)).
Fail Check (fun (x : Hx.Sig (Hx.SEq nat 0 0) (fun _ => Hx.Unit)) =>
  (eq_refl : x = Hx.pair _ _ (Hx.srefl nat 0) Hx.tt)).
(* Σ eta against a constructor (primitive record). *)
Check (fun (A : Type) (B : A -> Type) (p : Hx.Sig A B) =>
  (eq_refl : p = Hx.pair A B (Hx.fst A B p) (Hx.snd A B p))).
