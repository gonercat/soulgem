import Soulgem.Spec.WF
import Lean4Lean.Theory.VDecl

/-!
# Structure eta

The kernel's structure and unit eta apply to `is_non_rec_structure` types: one constructor, no
indices, not recursive (rc3 inductive.cpp:28, type_checker.cpp:863, 1123).
-/

namespace Soulgem.Spec
open Lean Lean4Lean

/-- Field `i`'s type mentions an earlier field (field `a < i` is the loose variable `i - 1 - a`). -/
def _root_.Soulgem.Spec.SCtor.fieldDep (c : SCtor) (i : Nat) : Bool :=
  (List.range i).any fun j => SBlock.hasVar (c.fields[i]!).ty j

/-- Field `i`'s type mentions only non-dependent earlier fields. -/
def _root_.Soulgem.Spec.SCtor.substField (c : SCtor) (i : Nat) : Bool :=
  (List.range i).all fun j => !SBlock.hasVar (c.fields[i]!).ty j || !c.fieldDep (i - 1 - j)

namespace SBlock
variable (b : SBlock)

/-- A fragment over `params ++ fields` placed at depth `D`, fields at level `d`. -/
def place' (d0 d D : Nat) (e : VExpr) : VExpr := place d0 (b.σ1 d) D e

/-- The constructor of a structure-like block whose recursor is large-eliminating. -/
def etaCtor? : Option SCtor :=
  match b.types with
  | [t] =>
    if t.indices.isEmpty && b.large then
      match t.ctors with
      | [c] =>
        if c.fields.all (fun f => f.cert matches .plain _ && !mentions b.names f.ty) &&
            (b.level.isNeverZero || !(List.range c.fields.length).any c.fieldDep) then some c
        else none
      | _ => none
    else none
  | _ => none

/-- The constructor's field telescope under `d` binders, field `a` at depth `d + a`. -/
def etaFields (c : SCtor) (d : Nat) : List VExpr :=
  (List.range c.fields.length).map fun a =>
    consumeAnn (b.place' (b.nparams + a) d (d + a) (c.fields[a]!).ty)

/-- The type of the `i`-th field of `z`, computed by recursion on `z`. -/
def etaFieldTy (c : SCtor) (d : Nat) (z : VExpr) (i : Nat) : VExpr :=
  let n := b.nparams
  let own := ownLevels b.uvars
  let f := c.fields[i]!
  let nf := c.fields.length
  let S := appN (.const (b.types[0]!).name own) (vars d 0 n)
  let minor := lamTel (b.etaFields c d) (b.place' (n + i) d (d + nf) f.ty)
  appN (.const (b.recName 0) (.succ f.sort :: own)) (vars d 0 n ++
      [.lam S (.sort f.sort), minor, z])

/-- `y`'s `i`-th projection as a recursor application, for the eta rule of an `etaCtor?` block. -/
def projV (c : SCtor) (d : Nat) (y : VExpr) (i : Nat) : VExpr :=
  let n := b.nparams
  let own := ownLevels b.uvars
  let f := c.fields[i]!
  let S := appN (.const (b.types[0]!).name own) (vars d 0 n)
  let minor := lamTel (b.etaFields c d) (var (d + c.fields.length) (d + i))
  let F := if !c.fieldDep i then b.place' (n + i) d (d + 1) f.ty
    else if b.large && b.level.isNeverZero && !c.substField i then
      b.etaFieldTy c (d + 1) (var (d + 1) d) i
    else subst (fun j => if h : j < i then
        have : i - 1 - j < i := by omega
        projV c (d + 1) (var (d + 1) d) (i - 1 - j)
      else var (d + 1) (n - 1 - (j - i))) f.ty
  appN (.const (b.recName 0) (if b.large then f.sort :: own else own))
    (vars d 0 n ++ [.lam S F, minor, y])
termination_by i

/-- Structure eta for a structure-like block, as a closed equation over `ps` and `x : S ps`. -/
def etaRule : Option VDefEq := do
  let c ← b.etaCtor?
  let n := b.nparams
  let own := ownLevels b.uvars
  let D := n + 1
  let Δ := b.params ++ [appN (.const (b.types[0]!).name own) (vars n 0 n)]
  let x := var D n
  let mk := appN (.const c.name own) (vars D 0 n ++ (List.range c.fields.length).map
      (b.projV c D x))
  return { uvars := b.uvars, lhs := lamTel Δ x, rhs := lamTel Δ mk,
           type := forallTel Δ (appN (.const (b.types[0]!).name own) (vars D 0 n)) }

/-- `nm i ps z` under `D'` binders, `z` the variable at level `L`. -/
def projApp (nm : Nat → Name) (D' L i : Nat) : VExpr :=
  appN (.const (nm i) (ownLevels b.uvars)) (vars D' 0 b.nparams ++ [var D' L])

/-- Field `i`'s type under `D'` binders, the earlier fields read through `nm`. -/
def fieldTyP (nm : Nat → Name) (c : SCtor) (D' L i : Nat) : VExpr :=
  let n := b.nparams
  let f := c.fields[i]!
  if !c.fieldDep i then b.place' (n + i) L D' f.ty
  else subst (fun j => if j < i then b.projApp nm D' L (i - 1 - j) else var D'
      (n - 1 - (j - i))) f.ty

/-- Projection function `i`'s type Tᵢ and value Lᵢ. -/
def projDefP (nm : Nat → Name) (c : SCtor) (i : Nat) : VExpr × VExpr :=
  let n := b.nparams
  let own := ownLevels b.uvars
  let D := n + 1
  let f := c.fields[i]!
  let Δ := b.params ++ [appN (.const (b.types[0]!).name own) (vars n 0 n)]
  let S := appN (.const (b.types[0]!).name own) (vars D 0 n)
  let minor := lamTel (b.etaFields c D) (var (D + c.fields.length) (D + i))
  let rec_ := appN (.const (b.recName 0) (if b.large then f.sort :: own else own))
    (vars D 0 n ++ [.lam S (b.fieldTyP nm c (D + 1) D i), minor, var D n])
  (forallTel Δ (b.fieldTyP nm c D n i), lamTel Δ rec_)

def projTyP (nm : Nat → Name) (c : SCtor) (i : Nat) : VExpr := (b.projDefP nm c i).1

def projValP (nm : Nat → Name) (c : SCtor) (i : Nat) : VExpr := (b.projDefP nm c i).2

/-- Projection function `i` named `n`, at Tᵢ with value Lᵢ. -/
def projDefVal (n : Name) (nm : Nat → Name) (c : SCtor) (i : Nat) : VDefVal :=
  { name := n, uvars := b.uvars, type := b.projTyP nm c i, value := b.projValP nm c i }

/-- The structure-eta equation `λ ps x, x ≡ λ ps x, S.mk ps (nm₀ ps x) … (nmₙ₋₁ ps x)`. -/
def etaRuleP (nm : Nat → Name) (c : SCtor) : VDefEq :=
  let n := b.nparams
  let own := ownLevels b.uvars
  let D := n + 1
  let Δ := b.params ++ [appN (.const (b.types[0]!).name own) (vars n 0 n)]
  { uvars := b.uvars, lhs := lamTel Δ (var D n),
    rhs := lamTel Δ (appN (.const c.name own) (vars D 0 n ++ (List.range c.fields.length).map
        (b.projApp nm D n))),
    type := forallTel Δ (appN (.const (b.types[0]!).name own) (vars D 0 n)) }

/-- The environment after a plain block: its rules (`SBlock.add`), then structure eta. -/
def addEta (env : VEnv) : VEnv :=
  match b.etaRule with
  | some r => env.addDefEq r
  | none => env

end SBlock
end Soulgem.Spec
