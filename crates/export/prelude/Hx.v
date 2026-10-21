(* Heather export prelude for Rocq/Coq (docs/export-fragment-design.md §4).

   The whole per-target trusted text of the export, mirroring prelude/Hx.lean
   constant for constant. Heather level l is Type@{Hx.u_l}: the library is
   universe-monomorphic, so closed levels are a chain of global universes
   (instances cannot be algebraic here).

   What each former relies on:
   - Nat: Coq's unary nat. A large numeral is a large term; the exporter
     refuses literals past a bound.
   - Id: a Type-valued inductive (no K, no irrelevance).
   - SEq: a record over an SProp equality with Definitional UIP, whose
     special reduction is Heather's strip rule. The record cannot be
     primitive (its only field is irrelevant), so neutral proofs compare
     only in eta-long form, as in Lean.
   - Sig: a primitive record (eta against a constructor).
   - Unit: an inductive. Coq has NO unit eta, and a record with no relevant
     field cannot be primitive: Heather's unit eta is the one rule this
     target lacks outright. The exporter works around it where it matters,
     a case over a singleton payload (caseL/caseR/caseLR below).
   - Wf: positivity and guard checks bypassed, the two assumptions
     Print Assumptions reports. *)

Set Universe Polymorphism.
Set Primitive Projections.
Set Definitional UIP.
Unset Universe Minimization ToSet.


Monomorphic Universe u1 u2 u3 u4.
Monomorphic Constraint Set < u1, u1 < u2, u2 < u3, u3 < u4.

Definition Nat := nat.
Definition succ (n : nat) : nat := S n.
Definition elimNat@{l} (M : nat -> Type@{l}) (b : M 0) (s : forall k, M k -> M (S k)) (n : nat) : M n :=
  nat_rect M b s n.

Definition the@{l} (A : Type@{l}) (a : A) : A := a.

Inductive Id@{l} (A : Type@{l}) (a : A) : A -> Type@{l} := refl_ : Id A a a.
Definition refl@{l} (A : Type@{l}) (a : A) : Id A a a := refl_ A a.
Definition J@{l l'} (A : Type@{l}) (a : A) (M : forall y : A, Id A a y -> Type@{l'})
  (c : M a (refl A a)) (b : A) (e : Id A a b) : M b e :=
  match e in Id _ _ y return M y e with refl_ _ _ => c end.

Inductive sEq@{l} (A : Type@{l}) (a : A) : A -> SProp := srefl_ : sEq A a a.
Unset Primitive Projections.
Record SEq@{l} (A : Type@{l}) (a b : A) : Type@{l} := mkSEq { pf : sEq A a b }.
Inductive sFalse : SProp := .
Record SEmpty@{l} : Type@{l} := mkSEmpty { epf : sFalse }.
Inductive sNonempty@{l} (A : Type@{l}) : SProp := sintro : A -> sNonempty A.
Record Squash@{l} (A : Type@{l}) : Type@{l} := mkSquash { spf : sNonempty A }.
Set Primitive Projections.
Arguments mkSEq {A a b} pf. Arguments pf {A a b} s.
Arguments mkSquash {A} spf. Arguments spf {A} s.

Definition srefl@{l} (A : Type@{l}) (a : A) : SEq A a a := mkSEq (srefl_ A a).
Definition transp@{l l'} (A : Type@{l}) (P : A -> Type@{l'}) (a b : A) (e : SEq A a b) (t : P a) : P b :=
  match pf e in sEq _ _ y return P y with srefl_ _ _ => t end.
Definition elimSEmpty@{l l'} (M : SEmpty@{l'} -> Type@{l}) (e : SEmpty@{l'}) : M e :=
  match epf e with end.
Definition squash@{l} (A : Type@{l}) (a : A) : Squash A := mkSquash (sintro A a).
(* The result is stated at the eta-long scrutinee: with no eta for this
   record, `B s` and `B (squash A x)` do not convert at a neutral `s`. The
   exporter writes every term at a Squash type eta-long, which makes the two
   statements agree. *)
(* A term at a squash type, eta-long: two of these convert by irrelevance of
   the SProp field, which a neutral and a constructor do not (no eta for a
   record with no relevant field). *)
Definition squashEta@{l} (A : Type@{l}) (s : Squash@{l} A) : Squash@{l} A := mkSquash (spf s).
Definition elimSquash@{l l'} (A : Type@{l}) (B : Squash A -> Type@{l'})
  (c : forall x : A, Squash (B (squash A x))) (s : Squash A) : Squash (B (mkSquash (spf s))) :=
  mkSquash (match spf s with sintro _ x => spf (c x) end).

Record Sig@{l l'} (A : Type@{l}) (B : A -> Type@{l'}) : Type@{max(l,l')} := mkSig { fst_ : A; snd_ : B fst_ }.
Definition pair@{l l'} (A : Type@{l}) (B : A -> Type@{l'}) (a : A) (b : B a) : Sig A B := mkSig A B a b.
Definition fst@{l l'} (A : Type@{l}) (B : A -> Type@{l'}) (p : Sig A B) : A := fst_ A B p.
Definition snd@{l l'} (A : Type@{l}) (B : A -> Type@{l'}) (p : Sig A B) : B (fst_ A B p) := snd_ A B p.

Inductive Unit@{l} : Type@{l} := tt_.
Definition tt@{l} : Unit@{l} := tt_.
Inductive Empty@{l} : Type@{l} := .
Definition elimEmpty@{l l'} (M : Empty@{l'} -> Type@{l}) (e : Empty@{l'}) : M e := match e with end.

Inductive Sum@{l l'} (A : Type@{l}) (B : Type@{l'}) : Type@{max(l,l')} := inl_ : A -> Sum A B | inr_ : B -> Sum A B.
Definition inl@{l l'} (A : Type@{l}) (B : Type@{l'}) (a : A) : Sum A B := inl_ A B a.
Definition inr@{l l'} (A : Type@{l}) (B : Type@{l'}) (b : B) : Sum A B := inr_ A B b.
Definition case@{l l' l''} (A : Type@{l}) (B : Type@{l'}) (M : Sum A B -> Type@{l''})
  (cl : forall x : A, M (inl A B x)) (cr : forall y : B, M (inr A B y)) (s : Sum A B) : M s :=
  match s with inl_ _ _ x => cl x | inr_ _ _ y => cr y end.

(* A case whose summand is a closed singleton (design §5.3). Coq has no unit
   eta, so the prelude's case cannot hand that branch `M (inl x)` at a bound
   `x` and expect `x` to convert with the canonical element. These state the
   branch at the canonical element `a` and reach it by J along
   `ea : forall x, a = x`, which Coq proves by destruct: it reduces whenever
   the payload is a constructor, and the exporter prints a payload of a
   closed singleton type as its canonical element. *)
Definition etaUnit@{l} (u : Unit@{l}) : Id@{l} Unit@{l} tt@{l} u := match u with tt_ => refl@{l} _ _ end.
Definition etaSEq@{l} (A : Type@{l}) (a : A) (p : SEq@{l} A a a) : Id@{l} (SEq@{l} A a a) (srefl@{l} A a) p :=
  match p with mkSEq q => refl@{l} _ _ end.
Definition etaSig@{l l' m | l <= m, l' <= m} (A : Type@{l}) (B : Type@{l'}) (a : A) (b : B)
  (ea : forall x : A, Id@{l} A a x) (eb : forall y : B, Id@{l'} B b y) (p : Sig@{l l'} A (fun _ => B)) :
  Id@{m} (Sig@{l l'} A (fun _ => B)) (pair@{l l'} A (fun _ => B) a b) p :=
  J@{l m} A a (fun x _ => Id@{m} (Sig@{l l'} A (fun _ => B)) (pair@{l l'} A (fun _ => B) a b) (pair@{l l'} A (fun _ => B) x (snd@{l l'} A (fun _ => B) p)))
    (J@{l' m} B b (fun y _ => Id@{m} (Sig@{l l'} A (fun _ => B)) (pair@{l l'} A (fun _ => B) a b) (pair@{l l'} A (fun _ => B) a y))
      (refl@{m} _ _) (snd@{l l'} A (fun _ => B) p) (eb (snd@{l l'} A (fun _ => B) p)))
    (fst@{l l'} A (fun _ => B) p) (ea (fst@{l l'} A (fun _ => B) p)).
Definition caseL@{l l' l''} (A : Type@{l}) (B : Type@{l'}) (a : A) (ea : forall x : A, Id@{l} A a x)
  (M : Sum@{l l'} A B -> Type@{l''}) (cl : M (inl A B a)) (cr : forall y : B, M (inr A B y)) (s : Sum A B) : M s :=
  match s with inl_ _ _ x => J@{l l''} A a (fun y _ => M (inl A B y)) cl x (ea x) | inr_ _ _ y => cr y end.
Definition caseR@{l l' l''} (A : Type@{l}) (B : Type@{l'}) (b : B) (eb : forall y : B, Id@{l'} B b y)
  (M : Sum@{l l'} A B -> Type@{l''}) (cl : forall x : A, M (inl A B x)) (cr : M (inr A B b)) (s : Sum A B) : M s :=
  match s with inl_ _ _ x => cl x | inr_ _ _ y => J@{l' l''} B b (fun z _ => M (inr A B z)) cr y (eb y) end.
Definition caseLR@{l l' l''} (A : Type@{l}) (B : Type@{l'}) (a : A) (b : B)
  (ea : forall x : A, Id@{l} A a x) (eb : forall y : B, Id@{l'} B b y)
  (M : Sum@{l l'} A B -> Type@{l''}) (cl : M (inl A B a)) (cr : M (inr A B b)) (s : Sum A B) : M s :=
  match s with
  | inl_ _ _ x => J@{l l''} A a (fun y _ => M (inl A B y)) cl x (ea x)
  | inr_ _ _ y => J@{l' l''} B b (fun z _ => M (inr A B z)) cr y (eb y)
  end.

Inductive W@{l l'} (A : Type@{l}) (B : A -> Type@{l'}) : Type@{max(l,l')} := sup_ (a : A) (f : B a -> W A B).
Definition sup@{l l'} (A : Type@{l}) (B : A -> Type@{l'}) (a : A) (f : B a -> W A B) : W A B := sup_ A B a f.
Definition elimW@{l l' l''} (A : Type@{l}) (B : A -> Type@{l'}) (M : W A B -> Type@{l''})
  (s : forall a f, (forall y : B a, M (f y)) -> M (sup A B a f)) : forall t, M t :=
  fix go t := match t with sup_ _ _ a f => s a f (fun y => go (f y)) end.

Fixpoint Vec@{l} (A : Type@{l}) (n : nat) : Type@{l} :=
  match n with O => Unit@{l} | S k => Sig@{l l} A (fun _ => Vec A k) end.
Fixpoint Fin (n : nat) : Type@{Set} :=
  match n with O => Empty@{Set} | S k => Sum@{Set Set} Unit@{Set} (Fin k) end.

