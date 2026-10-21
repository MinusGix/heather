/-
Heather export prelude for Lean 4 (docs/export-fragment-design.md §4).

This file is the whole per-target trusted text of the export: one constant
per kernel former, at the kernel's own argument order, so the exported
declarations are applications of these and nothing else. A Heather level
`l` is `Type l` (Russell universes: a code and the type it decodes to are
the same Lean term, so `El` disappears).

What each former relies on from Lean's kernel:
- `Nat`: the builtin, so literals are GMP literals.
- `Id`: a Type-valued inductive, so no K and no proof irrelevance.
- `SEq`: a one-field structure over `Eq`. Proof irrelevance and the K-like
  reduction of `Eq.rec` give Heather's strip rule; *irrelevance between two
  neutral proofs* additionally needs the exporter to write every proof in
  eta-long form `⟨p.pf⟩`, because Lean's structure eta only fires against a
  constructor.
- `Sig`, `Unit`: structures, so Σ-eta (against a constructor) and unit eta
  (always) are Lean's own.
- `Wf`: not definable here (the children `Vec (Wf S n) (n a)` are not a
  syntactically positive occurrence); the exporter refuses it.
-/
noncomputable section
namespace Hx
universe u v w

abbrev Nat := _root_.Nat
abbrev succ (n : Nat) : Nat := n.succ
abbrev elimNat (M : Nat → Type u) (b : M 0) (s : (k : Nat) → M k → M (k + 1)) (n : Nat) : M n :=
  @Nat.rec M b s n

abbrev the (A : Sort u) (a : A) : A := a

inductive Id (A : Type u) (a : A) : A → Type u
  | refl : Id A a a
abbrev refl (A : Type u) (a : A) : Id A a a := Id.refl
abbrev J (A : Type u) (a : A) (M : (y : A) → Id A a y → Type v) (c : M a (refl A a)) (b : A) (e : Id A a b) : M b e :=
  @Id.rec A a M c b e

structure SEq (A : Type u) (a b : A) : Type u where
  pf : a = b
abbrev srefl (A : Type u) (a : A) : SEq A a a := ⟨rfl⟩
abbrev transp (A : Type u) (P : A → Type v) (a b : A) (e : SEq A a b) (t : P a) : P b :=
  @Eq.rec A a (fun x _ => P x) t b e.pf

structure SEmpty : Type u where
  pf : False
abbrev elimSEmpty (M : SEmpty.{v} → Type u) (e : SEmpty.{v}) : M e := e.pf.elim

structure Squash (A : Type u) : Type u where
  pf : Nonempty A
abbrev squash (A : Type u) (a : A) : Squash A := ⟨⟨a⟩⟩
-- Rocq writes a squash term eta-long (`Hx.v`); Lean's η needs nothing.
abbrev squashEta (A : Type u) (s : Squash A) : Squash A := s
abbrev elimSquash (A : Type u) (B : Squash A → Type v) (c : (x : A) → Squash (B (squash A x)))
    (s : Squash A) : Squash (B s) :=
  ⟨@Nonempty.rec A (fun _ => Nonempty (B s)) (fun x => (c x).pf) s.pf⟩

structure Sig (A : Type u) (B : A → Type v) : Type (max u v) where
  mk ::
  fst : A
  snd : B fst
abbrev pair (A : Type u) (B : A → Type v) (a : A) (b : B a) : Sig A B := ⟨a, b⟩
abbrev fst (A : Type u) (B : A → Type v) (p : Sig A B) : A := p.1
abbrev snd (A : Type u) (B : A → Type v) (p : Sig A B) : B p.1 := p.2

structure Unit : Type u where
  mk ::
abbrev tt : Unit.{u} := ⟨⟩
inductive Empty : Type u
abbrev elimEmpty (M : Empty.{v} → Type u) (e : Empty.{v}) : M e := @Empty.rec M e

inductive Sum (A : Type u) (B : Type v) : Type (max u v)
  | inl : A → Sum A B
  | inr : B → Sum A B
abbrev inl (A : Type u) (B : Type v) (a : A) : Sum A B := Sum.inl a
abbrev inr (A : Type u) (B : Type v) (b : B) : Sum A B := Sum.inr b
abbrev case (A : Type u) (B : Type v) (M : Sum A B → Type w) (cl : (x : A) → M (inl A B x))
    (cr : (y : B) → M (inr A B y)) (s : Sum A B) : M s :=
  @Sum.rec A B M cl cr s

-- A `case` whose summand is a closed singleton (design §5.3): that branch is
-- stated at the canonical element `a`, and the case reaches it by `J` along
-- `ea : ∀ x, a = x`. Here every `etaX` is `refl` by Lean's own η, so the
-- case computes at a neutral payload too; Rocq needs the forms for real.
abbrev etaUnit (u : Unit.{w}) : Id Unit tt u := Id.refl
abbrev etaSEq (A : Type u) (a : A) (p : SEq A a a) : Id (SEq A a a) (srefl A a) p := Id.refl
-- Rocq's instance has a third level (the pair's, which Rocq cannot write as
-- `max`); the printers drop it here.
abbrev etaSig (A : Type u) (B : Type v) (a : A) (b : B) (ea : (x : A) → Id A a x) (eb : (y : B) → Id B b y)
    (p : Sig A (fun _ => B)) : Id (Sig A (fun _ => B)) (pair A (fun _ => B) a b) p :=
  J A a (fun x _ => Id (Sig A (fun _ => B)) (pair A (fun _ => B) a b) (pair A (fun _ => B) x p.2))
    (J B b (fun y _ => Id (Sig A (fun _ => B)) (pair A (fun _ => B) a b) (pair A (fun _ => B) a y)) Id.refl p.2 (eb p.2))
    p.1 (ea p.1)
abbrev caseL (A : Type u) (B : Type v) (a : A) (ea : (x : A) → Id A a x) (M : Sum A B → Type w)
    (cl : M (inl A B a)) (cr : (y : B) → M (inr A B y)) (s : Sum A B) : M s :=
  case A B M (fun x => J A a (fun y _ => M (inl A B y)) cl x (ea x)) cr s
abbrev caseR (A : Type u) (B : Type v) (b : B) (eb : (y : B) → Id B b y) (M : Sum A B → Type w)
    (cl : (x : A) → M (inl A B x)) (cr : M (inr A B b)) (s : Sum A B) : M s :=
  case A B M cl (fun y => J B b (fun z _ => M (inr A B z)) cr y (eb y)) s
abbrev caseLR (A : Type u) (B : Type v) (a : A) (b : B) (ea : (x : A) → Id A a x) (eb : (y : B) → Id B b y)
    (M : Sum A B → Type w) (cl : M (inl A B a)) (cr : M (inr A B b)) (s : Sum A B) : M s :=
  case A B M (fun x => J A a (fun y _ => M (inl A B y)) cl x (ea x)) (fun y => J B b (fun z _ => M (inr A B z)) cr y (eb y)) s

inductive W (A : Type u) (B : A → Type v) : Type (max u v)
  | sup (a : A) (f : B a → W A B) : W A B
abbrev sup (A : Type u) (B : A → Type v) (a : A) (f : B a → W A B) : W A B := W.sup a f
abbrev elimW (A : Type u) (B : A → Type v) (M : W A B → Type w)
    (s : (a : A) → (f : B a → W A B) → ((y : B a) → M (f y)) → M (sup A B a f)) (t : W A B) : M t :=
  @W.rec A B M s t

abbrev Vec (A : Type u) (n : Nat) : Type u :=
  @Nat.rec (fun _ => Type u) Unit.{u} (fun _ r => Sig A (fun _ => r)) n
abbrev Fin (n : Nat) : Type :=
  @Nat.rec (fun _ => Type) Empty.{0} (fun _ r => Sum Unit.{0} r) n

end Hx
end
