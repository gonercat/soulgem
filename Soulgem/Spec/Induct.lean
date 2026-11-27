import Soulgem.Spec.Level
import Lean4Lean.Theory.VEnv

/-!
# Specification of inductive blocks (mutual families)

A block is given with a certificate: the weak-head normal forms the kernel reads are supplied, and
`SBlock.WF` requires each to be definitionally equal to the declared term.
-/

namespace Soulgem.Spec
open Lean Lean4Lean

deriving instance DecidableEq for VExpr

/-- Rename free variables: index `i ≥ k` becomes `g (i - k) + k`. -/
def remap (g : Nat → Nat) : VExpr → (k : Nat := 0) → VExpr
  | .bvar i, k => if i < k then .bvar i else .bvar (g (i - k) + k)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (remap g f k) (remap g a k)
  | .lam A b, k => .lam (remap g A k) (remap g b (k + 1))
  | .forallE A b, k => .forallE (remap g A k) (remap g b (k + 1))

/-- Move `e` from under `d0` binders to under `d`, the binder at level `L` going to `σ L`. -/
def place (d0 : Nat) (σ : Nat → Nat) (d : Nat) (e : VExpr) : VExpr :=
  remap (fun i => d - 1 - σ (d0 - 1 - i)) e

/-- The variable bound at level `L`, seen under `d` binders. -/
def var (d L : Nat) : VExpr := .bvar (d - 1 - L)

/-- The variables at levels `L, L+1, …, L+n-1`, seen under `d` binders. -/
def vars (d L n : Nat) : List VExpr := (List.range n).map fun i => var d (L + i)

def appN (f : VExpr) (as : List VExpr) : VExpr := as.foldl .app f

def forallTel : List VExpr → VExpr → VExpr
  | [], R => R
  | A :: As, R => .forallE A (forallTel As R)

def lamTel : List VExpr → VExpr → VExpr
  | [], b => b
  | A :: As, b => .lam A (lamTel As b)

/-- `Expr.consumeTypeAnnotations`: the kernel's inductive checker strips each binder with it. -/
def consumeAnn : VExpr → VExpr
  | .app (.app (.const ``optParam _) A) _ => consumeAnn A
  | .app (.app (.const ``autoParam _) A) _ => consumeAnn A
  | .app (.const ``outParam _) A => consumeAnn A
  | .app (.const ``semiOutParam _) A => consumeAnn A
  | e => e

/-- `normalizes_to_zero` (level.cpp:174), Lean's `Level.isAlwaysZero`. -/
def _root_.Lean4Lean.VLevel.isAlwaysZero : VLevel → Bool
  | .zero => true
  | .param _ | .succ _ => false
  | .max a b => a.isAlwaysZero && b.isAlwaysZero
  | .imax _ b => b.isAlwaysZero

/-- How a constructor field's type decomposes after weak-head normalization. -/
inductive FieldCert where
  /-- no occurrence of the block's types; `w` is the normal form -/
  | plain (w : VExpr)
  /-- `∀ xs, I_k params idx` -/
  | recursive (xs : List VExpr) (k : Nat) (idx : List VExpr)
  deriving Inhabited

structure SField where
  /-- the binder type as written, under the parameters and the earlier fields -/
  ty : VExpr
  /-- `ty : Sort sort` -/
  sort : VLevel
  cert : FieldCert
  deriving Inhabited

structure SCtor where
  name : Name
  /-- the declared type: `∀ (parameter binders), ∀ fields, I params idx` -/
  type : VExpr
  fields : List SField
  /-- the result's indices, under the parameters and all fields -/
  idx : List VExpr
  deriving Inhabited

structure SType where
  name : Name
  type : VExpr
  /-- the index telescope after normalization, under the parameters -/
  indices : List VExpr
  ctors : List SCtor
  deriving Inhabited

structure SBlock where
  uvars : Nat
  /-- the parameter telescope after normalization (shared by all members) -/
  params : List VExpr
  /-- the common sort of the members -/
  level : VLevel
  types : List SType
  deriving Inhabited

namespace SBlock
variable (b : SBlock)

def nparams : Nat := b.params.length
def ntypes : Nat := b.types.length
def ctors : List SCtor := b.types.flatMap (·.ctors)
def nctors : Nat := b.ctors.length
/-- global index of the first constructor of member `j` -/
def ctorBase (j : Nat) : Nat := ((b.types.take j).map (·.ctors.length)).sum

/-- Not `elim_only_at_universe_zero` (inductive.cpp:522): the motive may target any universe. -/
def large : Bool :=
  b.level.isNeverZero ||
  match b.types with
  | [t] => match t.ctors with
    | [] => true
    | [c] =>
      let nf := c.fields.length
      let res := (List.range b.nparams).map (fun i => var (b.nparams + nf) i) ++ c.idx
      (List.range nf).all fun a =>
        (c.fields[a]!).sort.isAlwaysZero || res.contains (var (b.nparams + nf) (b.nparams + a))
    | _ => false
  | _ => false

/-- Universe parameters of the recursor: the motive's level comes first when large. -/
def recUvars : Nat := if b.large then b.uvars + 1 else b.uvars
def recLevels : List VLevel := (List.range b.recUvars).map .param
/-- The block's own universe parameters, as seen inside the recursor. -/
def blockLevels : List VLevel :=
  (List.range b.uvars).map fun i => .param (if b.large then i + 1 else i)
def elimSort : VExpr := .sort (if b.large then .param 0 else .zero)
/-- A fragment of the declaration, with its universe parameters moved to the recursor's. -/
def sh (e : VExpr) : VExpr := e.instL b.blockLevels
def binder (e : VExpr) : VExpr := consumeAnn (b.sh e)
def recName (j : Nat) : Name := .str (b.types[j]!).name "rec"
def tconst (j : Nat) : VExpr := .const (b.types[j]!).name b.blockLevels

/-- σ for a fragment over `params ++ (m locals)` placed with the locals starting at level `D`. -/
def σ1 (D : Nat) (L : Nat) : Nat := if L < b.nparams then L else L - b.nparams + D
/-- σ for a fragment over `params ++ fields<a ++ xs`, fields at `D`, xs at `E`. -/
def σ2 (a D E : Nat) (L : Nat) : Nat :=
  if L < b.nparams then L else if L < b.nparams + a then L - b.nparams + D
  else L - (b.nparams + a) + E

/-- Type of the motive for member `j`, placed at level `n + j`. -/
def motiveTy (j : Nat) : VExpr :=
  let n := b.nparams
  let D := n + j
  let Is := (b.types[j]!).indices
  let m := Is.length
  let idx := (List.range m).map fun a => b.binder (place (n + a) (b.σ1 D) (D + a) Is[a]!)
  let major := appN (b.tconst j) (vars (D + m) 0 n ++ vars (D + m) D m)
  forallTel idx (.forallE major b.elimSort)

/-- The positions of the recursive fields of `c`, with their certificates. -/
def _root_.Soulgem.Spec.SCtor.recFields (c : SCtor) :
    List (Nat × List VExpr × Nat × List VExpr) :=
  (List.range c.fields.length).filterMap fun a =>
    match (c.fields[a]!).cert with
    | .recursive xs k idx => some (a, xs, k, idx)
    | .plain _ => none

/-- Type of the minor premise for constructor `c` of member `j`, placed at level `D`. -/
def minorTy (j : Nat) (c : SCtor) (D : Nat) : VExpr :=
  let n := b.nparams
  let nf := c.fields.length
  let fs := (List.range nf).map fun a =>
    b.binder (place (n + a) (b.σ1 D) (D + a) (c.fields[a]!).ty)
  let R := c.recFields
  let ihs := (List.range R.length).map fun r =>
    let (a, xs, k, idx) := R[r]!
    let E := D + nf + r
    let nx := xs.length
    let xsP := (List.range nx).map fun e =>
      b.binder (place (n + a + e) (b.σ2 a D E) (E + e) xs[e]!)
    let d := E + nx
    let idxP := idx.map fun t => b.sh (place (n + a + nx) (b.σ2 a D E) d t)
    forallTel xsP (.app (appN (var d (n + k)) idxP) (appN (var d (D + a)) (vars d E nx)))
  let d := D + nf + R.length
  let idxP := c.idx.map fun t => b.sh (place (n + nf) (b.σ1 D) d t)
  let intro := appN (.const c.name b.blockLevels) (vars d 0 n ++ vars d D nf)
  forallTel (fs ++ ihs) (.app (appN (var d (n + j)) idxP) intro)

/-- The binders shared by every recursor of the block: parameters, motives, minor premises. -/
def preTel : List VExpr :=
  let n := b.nparams
  let K := b.ntypes
  (List.range n).map (fun i => b.binder b.params[i]!) ++
  (List.range K).map b.motiveTy ++
  (List.range K).flatMap fun j =>
    let cs := (b.types[j]!).ctors
    (List.range cs.length).map fun q => b.minorTy j cs[q]! (n + K + b.ctorBase j + q)

def pre : Nat := b.nparams + b.ntypes + b.nctors

/-- The type of `I_d.rec`. -/
def recType (d : Nat) : VExpr :=
  let n := b.nparams
  let M := b.pre
  let Is := (b.types[d]!).indices
  let m := Is.length
  let idx := (List.range m).map fun a => b.binder (place (n + a) (b.σ1 M) (M + a) Is[a]!)
  let major := appN (b.tconst d) (vars (M + m) 0 n ++ vars (M + m) M m)
  let e := M + m + 1
  forallTel (b.preTel ++ idx ++ [major])
    (.app (appN (var e (n + d)) (vars e M m)) (var e (M + m)))

/-- The pieces shared by the iota rule and the stored rule of the `q`-th constructor of `I_d`. -/
def rulePieces (d q : Nat) : List VExpr × List VExpr × List VExpr × VExpr × VExpr :=
  let n := b.nparams
  let M := b.pre
  let c := (b.types[d]!).ctors[q]!
  let nf := c.fields.length
  let D := M + nf
  let fs := (List.range nf).map fun a => b.sh (place (n + a) (b.σ1 M) (M + a) (c.fields[a]!).ty)
  let idxP := c.idx.map fun t => b.sh (place (n + nf) (b.σ1 M) D t)
  let intro := appN (.const c.name b.blockLevels) (vars D 0 n ++ vars D M nf)
  let ihs := c.recFields.map fun (a, xs, k, idx) =>
    let nx := xs.length
    let xsP := (List.range nx).map fun e =>
      b.binder (place (n + a + e) (b.σ2 a M D) (D + e) xs[e]!)
    let d' := D + nx
    let idxR := idx.map fun t => b.sh (place (n + a + nx) (b.σ2 a M D) d' t)
    lamTel xsP <| .app (appN (.const (b.recName k) b.recLevels) (vars d' 0 M ++ idxR))
      (appN (var d' (M + a)) (vars d' D nx))
  let rhs := appN (var D (n + b.ntypes + b.ctorBase d + q)) (vars D M nf ++ ihs)
  (fs, fs.map consumeAnn, idxP, intro, rhs)

/-- The iota rule of `I_d.rec` for the `q`-th constructor of `I_d`, as a closed equation. -/
def iota (d q : Nat) : VDefEq :=
  let (fs, _, idxP, intro, rhs) := b.rulePieces d q
  let D := b.pre + fs.length
  let Δ := b.preTel ++ fs
  let lhs := .app (appN (.const (b.recName d) b.recLevels) (vars D 0 b.pre ++ idxP)) intro
  { uvars := b.recUvars, lhs := lamTel Δ lhs, rhs := lamTel Δ rhs,
    type := forallTel Δ (.app (appN (var D (b.nparams + d)) idxP) intro) }

/-- The counterpart of the rule the kernel stores (`RecursorRule.rhs`). -/
def ruleRhs (d q : Nat) : VExpr :=
  let (_, fs', _, _, rhs) := b.rulePieces d q
  lamTel (b.preTel ++ fs') rhs

end SBlock
end Soulgem.Spec
