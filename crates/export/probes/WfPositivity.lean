/- Heather's `Wf` cannot be a Lean inductive: the children `Vec (Wf S n) (n a)`
   are a `Nat.rec` at a neutral arity, not a syntactically positive occurrence,
   and Lean has no positivity bypass for checked declarations. -/
def Vec (α : Type) : Nat → Type
  | 0 => PUnit
  | n+1 => α × Vec α n
#guard_msgs (drop error) in
inductive Wf (S : Type) (n : S → Nat) : Type
  | supf (a : S) (cs : Vec (Wf S n) (n a)) : Wf S n
