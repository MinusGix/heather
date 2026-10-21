/-
The kernel route for an export (docs/export-fragment-design.md §5.6): read
the hash-consed `.hxk` file `heather_export::print_kernel` writes and add each
declaration to an environment that imports `Hx`, through the kernel's
`addDecl` alone. No parser and no elaborator sees an exported term, so what
this accepts is what Lean's kernel accepts.

  LEAN_PATH=<dir with Hx.olean> lean --run Import.lean Sweep.hxk

Line format, tab-separated; node lines are numbered from 0 in order:
  v i        bound variable (de Bruijn index)
  s l        `Type l`
  p a b      `(x : #a) → #b`
  l a b      `fun (x : #a) => #b`
  a f x      application
  c n l…     prelude constant `Hx.n` at levels l…
  g k        an exported declaration, Heather key `k` (`nat::Nat::add`)
  n d        natural-number literal
  d k t v    definition `Heather.k : #t := #v` (reducible)
  ax k t     assumption `Heather.k : #t`
  x k why    skipped by the exporter
-/
import Lean
open Lean

def heatherName (key : String) : Name :=
  (key.splitOn "::").foldl Name.str `Heather

structure St where
  env : Environment
  nodes : Array Expr := #[]
  defs : Nat := 0
  axioms : Nat := 0
  skipped : Nat := 0
  failed : Nat := 0

def node (st : St) (s : String) : Except String Expr :=
  match s.toNat? with
  | some i => match st.nodes[i]? with
    | some e => .ok e
    | none => .error s!"node {i} not yet defined"
  | none => .error s!"bad node id {s}"

def lit (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"bad number {s}"

def add (st : St) (k : String) (decl : Declaration) : IO St := do
  match st.env.addDeclCore 0 decl none with
  | .ok env => match decl with
    | .axiomDecl _ => pure { st with env, axioms := st.axioms + 1 }
    | _ => pure { st with env, defs := st.defs + 1 }
  | .error ex =>
    let msg ← (ex.toMessageData {}).toString
    IO.eprintln s!"{heatherName k}: kernel rejected: {msg}"
    pure { st with failed := st.failed + 1 }

def step (st : St) (line : String) : IO St := do
  if line.isEmpty then return st
  let fs := line.splitOn "\t"
  let push (e : Except String Expr) : IO St := match e with
    | .ok e => pure { st with nodes := st.nodes.push e }
    | .error m => throw (IO.userError s!"{m} in: {line}")
  match fs with
  | ["v", i] => push (return .bvar (← lit i))
  | ["s", l] => push (return .sort (.succ (.ofNat (← lit l))))
  | ["p", a, b] => push (return .forallE `x (← node st a) (← node st b) .default)
  | ["l", a, b] => push (return .lam `x (← node st a) (← node st b) .default)
  | ["a", f, x] => push (return .app (← node st f) (← node st x))
  | "c" :: n :: ls => push (return .const (Name.str `Hx n) (← ls.mapM fun l => return .ofNat (← lit l)))
  | ["g", k] => push (return .const (heatherName k) [])
  | ["n", d] => push (return .lit (.natVal (← lit d)))
  | ["d", k, t, v] =>
    match (do pure (← node st t, ← node st v)) with
    | .ok (ty, val) => add st k (.defnDecl
        { name := heatherName k, levelParams := [], type := ty, value := val,
          hints := .abbrev, safety := .safe })
    | .error m => throw (IO.userError m)
  | ["ax", k, t] =>
    match node st t with
    | .ok ty => add st k (.axiomDecl { name := heatherName k, levelParams := [], type := ty, isUnsafe := false })
    | .error m => throw (IO.userError m)
  | "x" :: k :: why => do
    IO.eprintln s!"{heatherName k}: skipped: {String.intercalate "\t" why}"
    pure { st with skipped := st.skipped + 1 }
  | _ => throw (IO.userError s!"bad line: {line}")

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run Import.lean FILE.hxk"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Hx }] {} 0
  let mut st : St := { env }
  for line in (← IO.FS.lines path) do
    st ← step st line
  IO.println s!"kernel: {st.defs} definitions, {st.axioms} assumptions, {st.skipped} skipped, {st.failed} rejected"
  return if st.failed == 0 then 0 else 1
