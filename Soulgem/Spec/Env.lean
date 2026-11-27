import Soulgem.Spec.Cert
import Soulgem.Spec.Eta
import Soulgem.Base

/-!
# The specification's environments

`Admits base env rec`: `env` extends `base` by definitions, opaque constants, plain and nested
blocks and structure eta through projection functions; `rec` records the inductive blocks.
-/

namespace Soulgem.Spec
open Lean4Lean

section
variable (tr : Translated) (b : SBlock) (nuser : Nat)

/-- Admissibility of a nested declaration `u` translated to `tr`, over the earlier blocks `rec`. -/
def NestedWF (rec : List RBlock) (env : VEnv) (u : UDecl) (fams : List Fam) : Prop :=
  b.Certifies u.uvars u.nparams tr.types ∧ b.WF env ∧ RestoreSafe tr b nuser = true ∧
  AuxFresh b nuser env ∧ AuxMembers tr b nuser = true ∧ RecNames b nuser = true ∧
  ∃ envT, b.add env = some envT ∧
    FamsOK (certTr tr rec fams) b nuser rec envT fams ∧ CertsOK tr b nuser rec fams envT

end

/-- The record entry of a plain block. -/
def RBlock.plain (b : SBlock) : RBlock := { b, nuser := b.ntypes, tr := ⟨[], []⟩ }

inductive Admits (base : VEnv) : VEnv → List RBlock → Prop where
  | base : Admits base base []
  | «def» {env env' : VEnv} {rec : List RBlock} {ci : VDefVal} : Admits base env rec →
    DefWF env ci → env.addConst ci.name ci.toVConstant = some env' →
    Admits base (env'.addDefEq ci.toDefEq) rec
  | «opaque» {env env' : VEnv} {rec : List RBlock} {ci : VDefVal} : Admits base env rec →
    DefWF env ci → env.addConst ci.name ci.toVConstant = some env' → Admits base env' rec
  | plain {env env' : VEnv} {rec : List RBlock} {b : SBlock} : Admits base env rec →
    b.WF env → b.add env = some env' → Admits base (b.addEta env') (rec ++ [RBlock.plain b])
  /-- Structure eta through named projection functions: a constant per field of a plain block. -/
  | etaProj {env : VEnv} {rec : List RBlock} {b : SBlock} {c : SCtor} {nm : List Name} :
    Admits base env rec → RBlock.plain b ∈ rec → b.etaCtor? = some c → nm.length = c.fields.length →
    (∀ i < nm.length, env.constants (nm.getD i .anonymous) =
      some ⟨b.uvars, b.projTyP (nm.getD · .anonymous) c i⟩) →
    (∀ i < nm.length, (c.fields[i]!).sort.isAlwaysZero = false →
      env.defeqs (b.projDefVal (nm.getD i .anonymous) (nm.getD · .anonymous) c i).toDefEq) →
    Admits base (env.addDefEq (b.etaRuleP (nm.getD · .anonymous) c)) rec
  | nested {env env' : VEnv} {rec : List RBlock} {u : UDecl} {b : SBlock} {tr : Translated}
      {fams : List Fam} :
    Admits base env rec → elim (indOf rec) (fun c => (env.constants c).isSome) u = .ok tr →
    NestedWF tr b u.types.length rec env u fams → addNested tr b u.types.length env = some env' →
    Admits base (addCertified tr b u.types.length rec fams env')
      (rec ++ [{ b, nuser := u.types.length, tr }])

end Soulgem.Spec
