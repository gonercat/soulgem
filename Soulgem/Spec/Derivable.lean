import Soulgem.Spec.Env
import Soulgem.CoreModel

/-! # Derivable: what an admitted environment contains for a list of wants -/
open Lean4Lean Soulgem Soulgem.Spec

set_option autoImplicit false

namespace Soulgem.Spec

/-- The names the recorded block's admission declares, never its auxiliary types or constructors. -/
def RBlock.declNames (r : RBlock) : List Lean.Name :=
  (r.b.types.take r.nuser).map (·.name) ++ ((r.b.types.take r.nuser).flatMap
      (·.ctors)).map (·.name) ++
    (nestedRecs r.tr r.b r.nuser).map (·.name)

inductive Want where
  | defn (ci : VDefVal)
  | opaq (ci : VDefVal)
  | block (members : List (Lean.Name × VConstant))
  | check (n : Lean.Name) (c : VConstant)

def Want.Holds (env : VEnv) (rec : List RBlock) : Want → Prop
  | .defn ci => env.constants ci.name = some ci.toVConstant ∧ env.defeqs ci.toDefEq
  | .opaq ci => env.constants ci.name = some ci.toVConstant
  | .block ms => (∀ m ∈ ms, env.constants m.1 = some m.2) ∧
      ∃ r ∈ rec, ∀ m ∈ ms, m.1 ∈ r.declNames
  | .check n c => env.constants n = some c

def Derivable (Γ : List Want) : Prop :=
  ∃ (env : VEnv) (rec : List RBlock), Admits Core.coreEnv env rec ∧ ∀ w ∈ Γ, w.Holds env rec

end Soulgem.Spec
