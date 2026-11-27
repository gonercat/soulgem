import Soulgem.Spec.Nested
import Lean4Lean.Theory.Typing.Basic

/-!
# Well-formedness and the environment extension

`SBlock.WF b env`: Spec's conditions on a mutual block, after the kernel's `check_inductive_types`
and `check_constructors`, with each weak-head normal form supplied by a certificate.
-/

namespace Soulgem.Spec
open Lean Lean4Lean

/-- `A` and `B` are definitionally equal types. -/
def DefEqTy (env : VEnv) (U : Nat) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∃ u, env.IsDefEq U Γ A B (.sort u)

/-- Stripping `optParam`/`autoParam`/`outParam`/`semiOutParam` (`consumeAnn`) preserves the type. -/
def AnnOK (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  DefEqTy env U Γ e (consumeAnn e)

/-- `a ≤ b` under every assignment of the universe parameters. -/
def LevelLE (a b : VLevel) : Prop := ∀ ls, a.eval ls ≤ b.eval ls

/-- The block's own universe parameters, `.param 0 … .param (U-1)`. -/
def ownLevels (U : Nat) : List VLevel := (List.range U).map .param

/-- Simultaneous substitution: variable `i ≥ k` becomes `f (i - k)`, lifted past `k` binders. -/
def subst (f : Nat → VExpr) : VExpr → (k : Nat := 0) → VExpr
  | .bvar i, k => if i < k then .bvar i else (f (i - k)).liftN k
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app g a, k => .app (subst f g k) (subst f a k)
  | .lam A b, k => .lam (subst f A k) (subst f b (k + 1))
  | .forallE A b, k => .forallE (subst f A k) (subst f b (k + 1))

namespace SBlock
variable (b : SBlock)

def names : List Name := b.types.map (·.name)

/-- `I_k params idx` under `d` binders, the parameters outermost. -/
def indApp (k d : Nat) (idx : List VExpr) : VExpr :=
  appN (.const (b.types[k]!).name (ownLevels b.uvars)) (vars d 0 b.nparams ++ idx)

/-- The environment in which constructors are checked: the block's types declared. -/
def withTypes (env : VEnv) : Option VEnv :=
  b.types.foldlM (fun e t => e.addConst t.name { uvars := b.uvars, type := t.type }) env

/-- The type of the `l`-th index argument of `I_j params idx`, in a context with `extra` binders. -/
def idxType (j extra : Nat) (idx : List VExpr) (l : Nat) : VExpr :=
  subst (fun i => if i < l then idx[l - 1 - i]! else .bvar (extra + (i - l)))
    ((b.types[j]!).indices[l]!)

/-- The loose variable `i` occurs in `e`. -/
def hasVar : VExpr → Nat → Bool
  | .bvar j, i => j == i
  | .sort _, _ | .const .., _ => false
  | .app f a, i => hasVar f i || hasVar a i
  | .lam A b, i | .forallE A b, i => hasVar A i || hasVar b (i + 1)

/-- The normal forms of the later fields do not mention the recursive field `a`. -/
def _root_.Soulgem.Spec.SCtor.recIndep (c : SCtor) : Bool :=
  (List.range c.fields.length).all fun a =>
    match (c.fields[a]!).cert with
    | .plain _ => true
    | .recursive .. => (List.range c.fields.length).all fun a' =>
      a' ≤ a || match (c.fields[a']!).cert with
        | .plain w => !hasVar w (a' - a - 1)
        | .recursive xs _ _ => (List.range xs.length).all fun e => !hasVar xs[e]! (a' - a - 1 + e)

/-- The syntactic conditions on one field's certificate. -/
def FieldSyn (f : SField) : Prop :=
  match f.cert with
  | .plain w => mentions b.names w = false
  | .recursive xs k idx =>
    k < b.ntypes ∧ idx.length = (b.types[k]!).indices.length ∧
    (∀ x ∈ xs, mentions b.names x = false) ∧ ∀ i ∈ idx, mentions b.names i = false

/-- The shape the kernel reads syntactically: parameter binders, fields, `I_j params idx`. -/
structure CtorSyn (j : Nat) (c : SCtor) : Prop where
  shape : (stripPi b.nparams c.type).map (·.2) =
    some (forallTel (c.fields.map (·.ty)) (b.indApp j (b.nparams + c.fields.length) c.idx))
  idx_len : c.idx.length = (b.types[j]!).indices.length
  idx_free : ∀ i ∈ c.idx, mentions b.names i = false
  recIndep : c.recIndep = true
  fields : ∀ f ∈ c.fields, b.FieldSyn f

structure Syn : Prop where
  nonempty : b.types ≠ []
  /-- every type and constructor name of the block is distinct. -/
  nodup : (b.names ++ b.ctors.map (·.name)).Nodup
  ctors : ∀ j < b.ntypes, ∀ c ∈ (b.types[j]!).ctors, b.CtorSyn j c

/-! ### The typing part -/

/-- The parameter binder types of a constructor type. -/
def _root_.Soulgem.Spec.SCtor.paramTys (c : SCtor) (n : Nat) : List VExpr :=
  ((stripPi n c.type).map (·.1)).getD []

/-- Strict positivity and the decomposition of one field, in context `Γ` (of length `d`). -/
def FieldOK (env : VEnv) (Γ : List VExpr) (d : Nat) (f : SField) : Prop :=
  match f.cert with
  | .plain w => DefEqTy env b.uvars Γ f.ty w
  | .recursive xs k idx =>
    DefEqTy env b.uvars Γ f.ty (forallTel xs (b.indApp k (d + xs.length) idx)) ∧
    (∀ e < xs.length, AnnOK env b.uvars ((xs.take e).reverse ++ Γ) xs[e]!) ∧
    (∀ l < idx.length, env.HasType b.uvars (xs.reverse ++ Γ) idx[l]!
      (b.idxType k (d - b.nparams + xs.length) idx l)) ∧
    ∀ e < xs.length, ∃ u, env.HasType b.uvars ((xs.take e).reverse ++ Γ) xs[e]! (.sort u) ∧
      ∀ ls, b.level.eval ls ≠ 0 → u.eval ls ≤ b.level.eval ls

/-- The context of field `a` of `c`: the parameters, then the earlier fields. -/
def fieldCtx (c : SCtor) (a : Nat) : List VExpr :=
  (b.params ++ (c.fields.take a).map (·.ty)).reverse

/-- The typing conditions on one constructor of member `j`, checked in `env`. -/
structure CtorOK (env : VEnv) (j : Nat) (c : SCtor) : Prop where
  typed : env.IsType b.uvars [] c.type
  params : ∀ i < b.nparams,
    DefEqTy env b.uvars (b.params.take i).reverse (c.paramTys b.nparams)[i]! b.params[i]!
  idx_typed : ∀ l < c.idx.length, env.HasType b.uvars (b.params ++ c.fields.map (·.ty)).reverse
    c.idx[l]! (b.idxType j c.fields.length c.idx l)
  fields : ∀ a < c.fields.length,
    env.HasType b.uvars (b.fieldCtx c a) (c.fields[a]!).ty (.sort (c.fields[a]!).sort) ∧
    AnnOK env b.uvars (b.fieldCtx c a) (c.fields[a]!).ty ∧
    (b.level.isAlwaysZero ∨ LevelLE (c.fields[a]!).sort b.level) ∧
    b.FieldOK env (b.fieldCtx c a) (b.nparams + a) (c.fields[a]!)

/-- `check_inductive_types` and `check_constructors`. -/
structure WF (env : VEnv) : Prop where
  syn : b.Syn
  level : b.level.WF b.uvars
  params : ∀ i < b.nparams, env.IsType b.uvars (b.params.take i).reverse b.params[i]! ∧
    AnnOK env b.uvars (b.params.take i).reverse b.params[i]!
  types : ∀ t ∈ b.types,
    (∀ a < t.indices.length,
      env.IsType b.uvars ((b.params ++ t.indices.take a).reverse) t.indices[a]! ∧
      AnnOK env b.uvars ((b.params ++ t.indices.take a).reverse) t.indices[a]!) ∧
    DefEqTy env b.uvars [] t.type (forallTel (b.params ++ t.indices) (.sort b.level))
  ctors : ∃ env₁, b.withTypes env = some env₁ ∧
    ∀ j < b.ntypes, ∀ c ∈ (b.types[j]!).ctors, b.CtorOK env₁ j c

/-- The constants and rules the block adds: types, constructors, recursors, iota rules. -/
def add (env : VEnv) : Option VEnv := do
  let env ← b.withTypes env
  let env ← b.ctors.foldlM (fun e c => e.addConst c.name { uvars := b.uvars, type := c.type }) env
  let env ← (List.range b.ntypes).foldlM
    (fun e d => e.addConst (b.recName d) { uvars := b.recUvars, type := b.recType d }) env
  return (List.range b.ntypes).foldl (fun e d =>
    (List.range (b.types[d]!).ctors.length).foldl (fun e q => e.addDefEq (b.iota d q)) e) env

end SBlock

/-- The certified block's skeleton is the declaration: same members, types and constructors. -/
def SBlock.Certifies (b : SBlock) (uvars nparams : Nat) (ts : List UType) : Prop :=
  b.uvars = uvars ∧ b.nparams = nparams ∧
  b.types.map (fun t => (t.name, t.type, t.ctors.map fun c => (c.name, c.type))) =
    ts.map (fun t => (t.name, t.type, t.ctors))

/-- A key's arguments as a substitution for the container's parameters. -/
def argSubst (Ds : List VExpr) (i : Nat) : VExpr :=
  if h : i < Ds.length then Ds.reverse[i]'(by simpa using h) else .bvar (i - Ds.length)

/-- A container term at a key: levels instantiated by `lv`, parameters replaced by `Ds`. -/
def atKey (lv : List VLevel) (Ds : List VExpr) (k : Nat) (e : VExpr) : VExpr :=
  subst (argSubst Ds) (e.instL lv) k

/-- `as[i]` is `bs[i]` at the key under `k + i` further binders: a telescope at a key. -/
def EqLTel (lv : List VLevel) (Ds : List VExpr) : Nat → List VExpr → List VExpr → Prop
  | _, [], [] => True
  | k, a :: as, b :: bs => a.EqL (atKey lv Ds k b) ∧ EqLTel lv Ds (k + 1) as bs
  | _, _, _ => False

/-- Slot `σ` of a recorded block as a key, open over the block's parameters. -/
def RBlock.slotKey (r : RBlock) (σ : Nat) : Option VExpr :=
  if σ < r.nuser then (r.b.types[σ]?).map fun t =>
      appN (.const t.name (ownLevels r.b.uvars)) (vars r.b.nparams 0 r.b.nparams)
  else (r.tr.aux[σ - r.nuser]?).map (·.key)

/-- A family: `rec[ri]` at levels `lv` and parameter arguments `Ds`; `φ[σ]` indexes `tr.aux`. -/
structure Fam where
  ri : Nat
  lv : List VLevel
  Ds : List VExpr
  φ : List Nat
  kernelDs : Option (List VExpr) := none
  deriving Inhabited

variable (tr : Translated) (b : SBlock) (nuser : Nat)

/-- The auxiliary types and their constructors, which the final environment never declares. -/
def auxNames : List Name :=
  tr.aux.map (·.name) ++ (b.types.drop nuser).flatMap (·.ctors.map (·.name))

/-- Field `fb` of our constructor reads field `fJ` (position `k`) of the container's constructor. -/
def FieldCorr (F : Fam) (earlier : List Nat) (r : RBlock) (k : Nat) (fb fJ : SField) : Prop :=
  match fJ.cert, fb.cert with
  | .recursive xs m idx, .recursive xs' s idx' =>
    (∃ g, F.φ[m]? = some g ∧ s = nuser + g) ∧ EqLTel F.lv F.Ds k xs' xs ∧
    List.Forall₂ (fun e e' => e.EqL (atKey F.lv F.Ds (k + xs.length) e')) idx' idx
  | .recursive .., .plain _ => False
  | .plain _, _ =>
    (tr.restoreBody [] b.nparams fb.ty (b.nparams + k)).EqL (atKey F.lv F.Ds k fJ.ty) ∧
    mentions r.b.names fJ.ty = false ∧
    ∀ g a, tr.aux[g]? = some a → mentions [a.name] fb.ty → g ∈ earlier

/-- Our constructor `cb` of auxiliary `a` reads the container's constructor `cJ` of `tJ`. -/
def CtorCorr (F : Fam) (earlier : List Nat) (r : RBlock) (a : Aux) (tJ : SType)
    (cb cJ : SCtor) : Prop :=
  cb.name = cJ.name.replacePrefix tJ.name a.name ∧
  cb.name.replacePrefix a.name tJ.name = cJ.name ∧
  cb.fields.length = cJ.fields.length ∧
  List.Forall₂ (fun e e' => e.EqL (atKey F.lv F.Ds cb.fields.length e')) cb.idx cJ.idx ∧
  ∀ k (h : k < cb.fields.length) (h' : k < cJ.fields.length),
    FieldCorr tr b nuser F earlier r k cb.fields[k] cJ.fields[k]

/-- The names a family's arguments `Ds` may not mention. -/
def keyHidden : List Name :=
  auxNames tr b nuser ++ (List.range b.ntypes).map b.recName

/-- Each auxiliary type of family `F` is the recorded block's slot at the arguments `Ds`. -/
def KeysAt (F : Fam) (Ds : List VExpr) (r : RBlock) : Prop :=
  ∀ σ (hσ : σ < F.φ.length), ∃ a key, tr.aux[F.φ[σ]]? = some a ∧ r.slotKey σ = some key ∧
    a.key.EqL (atKey F.lv Ds 0 key)

/-- Family `F` checked against its recorded block `r`, slot by slot. -/
def FamAt (earlier : List Nat) (F : Fam) (r : RBlock) : Prop :=
  F.φ.length = r.b.ntypes ∧ F.Ds.length = r.b.nparams ∧ F.lv.length = r.b.uvars ∧
  b.level ≈ r.b.level.inst F.lv ∧ (∀ D ∈ F.Ds, mentions (keyHidden tr b nuser) D = false) ∧
  KeysAt tr F F.Ds r ∧
  ∀ σ (hσ : σ < F.φ.length), ∃ a t tJ,
    tr.aux[F.φ[σ]]? = some a ∧ b.types[nuser + F.φ[σ]]? = some t ∧ r.b.types[σ]? = some tJ ∧
    EqLTel F.lv F.Ds 0 t.indices tJ.indices ∧
    t.ctors.length = tJ.ctors.length ∧
    ∀ q (h : q < t.ctors.length) (h' : q < tJ.ctors.length),
      CtorCorr tr b nuser F earlier r a tJ t.ctors[q] tJ.ctors[q]

/-- The auxiliary types the families stand for. -/
def images (fams : List Fam) : List Nat := fams.flatMap (·.φ)

/-- The arguments `Ds` fit the parameter telescope `Ps` (outermost first). -/
def ArgsTyped (env : VEnv) (U : Nat) (Γ : List VExpr) (Ps Ds : List VExpr) : Prop :=
  Ds.length = Ps.length ∧ ∀ i (h : i < Ds.length) (h' : i < Ps.length),
    env.HasType U Γ Ds[i] (subst (argSubst (Ds.take i)) Ps[i] 0)

/-- Every family passes against its recorded block, slot by slot, in `envT`. -/
def FamsOK (rec : List RBlock) (envT : VEnv) (fams : List Fam) : Prop :=
  (∀ j (h : j < fams.length), ∃ r, rec[fams[j].ri]? = some r ∧
    FamAt tr b nuser (images (fams.take j)) fams[j] r ∧
    ArgsTyped envT b.uvars b.params.reverse (r.b.params.map (·.instL fams[j].lv)) fams[j].Ds) ∧
  (images fams).Perm (List.range tr.aux.length)

/-- Every term that gets restored applies auxiliary names only to the parameter variables. -/
def RestoreSafe : Bool :=
  let ns := auxNames tr b nuser
  let ms := ns ++ (List.range (b.ntypes - nuser)).map fun i => b.recName (nuser + i)
  let n := b.nparams
  b.types.all (·.ctors.all fun c => restoreSafeTop ns ms (ownLevels b.uvars) n c.type) &&
  (List.range b.ntypes).all fun d =>
    restoreSafeTop ns ms b.blockLevels n (b.recType d) &&
    (List.range (b.types[d]!).ctors.length).all fun q =>
      let r := b.iota d q
      restoreSafeTop ns ms b.blockLevels n r.lhs && restoreSafeTop ns ms b.blockLevels n r.rhs &&
      restoreSafeTop ns ms b.blockLevels n r.type

/-- The nested declaration translated to `tr` and certified by `b`, declared. -/
def addNested (env : VEnv) : Option VEnv := do
  let recs := nestedRecs tr b nuser
  let env ← (b.types.take nuser).foldlM
    (fun e t => e.addConst t.name ({ uvars := b.uvars, type := t.type } : VConstant)) env
  let env ← ((b.types.take nuser).flatMap (·.ctors)).foldlM
    (fun e c => e.addConst c.name
      ({ uvars := b.uvars, type := tr.restore [] b.nparams c.type } : VConstant)) env
  let env ← recs.foldlM
    (fun e r => e.addConst r.name ({ uvars := b.recUvars, type := r.type } : VConstant)) env
  return (recs.flatMap (·.iota)).foldl (fun e df => e.addDefEq df) env

/-- The members after the user's are the auxiliary types, in the translation table's order. -/
def AuxMembers : Bool :=
  (b.types.drop nuser).map (·.name) == tr.aux.map (·.name)

/-- The auxiliary constructors and recursors have names fresh for the environment. -/
def AuxFresh (env : VEnv) : Prop :=
  ((b.types.drop nuser).all fun t => t.ctors.all fun c => (env.constants c.name).isNone) ∧
  (List.range (b.ntypes - nuser)).all fun i => (env.constants (b.recName (nuser + i))).isNone

/-- The final auxiliary recursor names are distinct from each other and from the block's names. -/
def RecNames : Bool :=
  decide (((auxRecTable b nuser).map (·.2) ++ b.names ++ b.ctors.map (·.name) ++
    (List.range b.ntypes).map b.recName).Nodup)

end Soulgem.Spec
