import Soulgem.Spec.WF

/-!
# Certificates

A family with `kernelDs = some Ks` carries a certificate: `certTr` replaces its auxiliaries' keys
and `CertsOK` checks it in `certEnv`.
-/

namespace Soulgem.Spec
open Lean Lean4Lean

variable (tr : Translated) (b : SBlock) (nuser : Nat)

/-- The key a certified family gives auxiliary `g`: its slot key at the certificate. -/
def certKey (rec : List RBlock) (fams : List Fam) (g : Nat) : Option VExpr :=
  fams.findSome? fun F => if F.kernelDs.isNone then none else do
    let σ ← F.φ.findIdx? (· == g)
    let r ← rec[F.ri]?
    let key ← r.slotKey σ
    pure (atKey F.lv F.Ds 0 key)

/-- The translation with each certified auxiliary's key replaced by its certificate key. -/
def certTr (rec : List RBlock) (fams : List Fam) : Translated :=
  { tr with aux := tr.aux.mapIdx fun g a => { a with key := (certKey rec fams g).getD a.key } }

/-- `x` applied to the block's parameters, under λ-binders for them. -/
def etaParams (x : Name) : VExpr :=
  lamTel b.params (appN (.const x (ownLevels b.uvars)) (vars b.nparams 0 b.nparams))

/-- The checking environment for key arguments that name the block's recursors. -/
def certEnv (rec : List RBlock) (fams : List Fam) (envT : VEnv) : Option VEnv := do
  let e ← (auxRecTable b nuser).foldlM (fun e p => do
      let ci ← envT.constants p.1
      let e ← e.addConst p.2 ci
      let lv := ownLevels ci.uvars
      pure (e.addDefEq { uvars := ci.uvars, lhs := .const p.2 lv, rhs := .const p.1 lv,
                         type := ci.type })) envT
  (auxNames tr b nuser).foldlM (fun e x => do
      let ci ← envT.constants x
      pure (e.addDefEq { uvars := b.uvars, lhs := etaParams b x,
                         rhs := (certTr tr rec fams).restore [] b.nparams (etaParams b x),
                         type := ci.type })) e

/-- `F`'s certificate: kernel key arguments `Ks` naming no auxiliary and converting to `F.Ds`. -/
def CertOK (E : VEnv) (F : Fam) (Ks : List VExpr) (r : RBlock) : Prop :=
  let Ps := r.b.params.map (·.instL F.lv)
  Ks.length = Ps.length ∧
  (∀ K ∈ Ks, mentions (auxNames tr b nuser ++ (auxRecTable b nuser).map (·.1)) K = false) ∧
  (∀ i (h : i < Ks.length) (h' : i < F.Ds.length) (h'' : i < Ps.length),
    E.IsDefEq b.uvars b.params.reverse Ks[i] F.Ds[i] (subst (argSubst (Ks.take i)) Ps[i] 0)) ∧
  KeysAt tr F Ks r

/-- Every certified family passes `CertOK` against its recorded block, in `certEnv`. -/
def CertsOK (rec : List RBlock) (fams : List Fam) (envT : VEnv) : Prop :=
  ∀ j (h : j < fams.length) Ks, fams[j].kernelDs = some Ks →
    ∃ E r, certEnv tr b nuser rec fams envT = some E ∧ rec[fams[j].ri]? = some r ∧
      CertOK tr b nuser E fams[j] Ks r

/-- The typings of a certified declaration's constants at their certified types. -/
def certTypings (rec : List RBlock) (fams : List Fam) : List VDefEq :=
  if fams.all (·.kernelDs.isNone) then [] else
  let trC := certTr tr rec fams
  let refl (U : Nat) (x : Name) (τ : VExpr) : VDefEq :=
    { uvars := U, lhs := .const x (ownLevels U), rhs := .const x (ownLevels U), type := τ }
  ((b.types.take nuser).flatMap (·.ctors)).map (fun c =>
      refl b.uvars c.name (trC.restore [] b.nparams c.type)) ++
    (nestedRecs trC b nuser).map (fun r => refl b.recUvars r.name r.type) ++
    (nestedRecs trC b nuser).flatMap (·.iota)

/-- `env'` with a certified declaration's typings (`certTypings`) added. -/
def addCertified (rec : List RBlock) (fams : List Fam) (env' : VEnv) : VEnv :=
  (certTypings tr b nuser rec fams).foldl VEnv.addDefEq env'

end Soulgem.Spec
