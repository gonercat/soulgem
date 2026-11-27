import Lean4Lean.Theory.VExpr

/-!
# The kernel's level instantiation

`instK` follows `level.cpp`'s `instantiate` with its `mk_max` and `mk_imax` simplifications, which
the kernel skips when neither argument changed (pointer equality, `update_max`, level.cpp:308).
-/

namespace Lean4Lean
deriving instance DecidableEq for VLevel
end Lean4Lean

namespace Lean4Lean.VLevel

/-- `is_not_zero` (level.cpp:160), Lean's `Level.isNeverZero`: syntactically nonzero. -/
def isNeverZero : VLevel → Bool
  | .zero | .param _ => false
  | .succ _ => true
  | .max a b => a.isNeverZero || b.isNeverZero
  | .imax _ b => b.isNeverZero

def hasParam : VLevel → Bool
  | .zero => false
  | .param _ => true
  | .succ l => l.hasParam
  | .max a b | .imax a b => a.hasParam || b.hasParam

/-- `is_explicit`: `succ^k zero`; returns `k`. -/
def explicitDepth? : VLevel → Option Nat
  | .zero => some 0
  | .succ l => l.explicitDepth?.map (· + 1)
  | _ => none

/-- `to_offset`: `succ^k l` with `l` not a successor, as `(l, k)`. -/
def toOffset : VLevel → VLevel × Nat
  | .succ l => let (b, k) := l.toOffset; (b, k + 1)
  | l => (l, 0)

/-- `l` is `max a b` with `x` one of `a`, `b`. -/
def maxHas (l x : VLevel) : Bool :=
  match l with
  | .max a b => a == x || b == x
  | _ => false

/-- `mk_max`, case for case. -/
def mkMax (l1 l2 : VLevel) : VLevel :=
  match l1.explicitDepth?, l2.explicitDepth? with
  | some d1, some d2 => if d1 ≥ d2 then l1 else l2
  | _, _ =>
    if l1 = l2 then l1
    else if l1 = .zero then l2
    else if l2 = .zero then l1
    else if l2.maxHas l1 then l2
    else if l1.maxHas l2 then l1
    else if l1.toOffset.1 = l2.toOffset.1 then (if l1.toOffset.2 > l2.toOffset.2 then l1 else l2)
    else .max l1 l2

/-- `mk_imax`, case for case (`is_not_zero` is `isNeverZero`). -/
def mkIMax (l1 l2 : VLevel) : VLevel :=
  if l2.isNeverZero then mkMax l1 l2
  else if l2 = .zero then l2
  else if l1 = .zero ∨ l1 = .succ .zero then l2
  else if l1 = l2 then l1
  else .imax l1 l2

/-- `instantiate`: parameters by position, out-of-range parameters kept. -/
def instK (ls : List VLevel) : VLevel → VLevel
  | .zero => .zero
  | .param i => ls.getD i (.param i)
  | .succ l => if l.hasParam then .succ (instK ls l) else .succ l
  | .max a b => if a.hasParam || b.hasParam then mkMax (instK ls a) (instK ls b) else .max a b
  | .imax a b => if a.hasParam || b.hasParam then mkIMax (instK ls a) (instK ls b) else .imax a b

end Lean4Lean.VLevel

namespace Lean4Lean.VExpr
/-- Level instantiation of a term by `instK`. -/
def instLK (ls : List VLevel) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.instK ls)
  | .const c us => .const c (us.map (·.instK ls))
  | .app f a => .app (f.instLK ls) (a.instLK ls)
  | .lam A b => .lam (A.instLK ls) (b.instLK ls)
  | .forallE A b => .forallE (A.instLK ls) (b.instLK ls)
end Lean4Lean.VExpr

namespace Lean4Lean.VExpr
/-- Equal shape, corresponding levels equivalent (equal under every assignment). -/
def EqL : VExpr → VExpr → Prop
  | .bvar i, .bvar j => i = j
  | .sort u, .sort v => u ≈ v
  | .const c us, .const d vs => c = d ∧ List.Forall₂ (· ≈ ·) us vs
  | .app f a, .app g b => EqL f g ∧ EqL a b
  | .lam A b, .lam B c => EqL A B ∧ EqL b c
  | .forallE A b, .forallE B c => EqL A B ∧ EqL b c
  | _, _ => False
end Lean4Lean.VExpr
