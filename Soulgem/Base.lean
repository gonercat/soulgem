import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic
/-!
# Base definitions shared by the specification and the model

Restated from upstream lean4lean's `Lean4Lean.Theory.Typing.Env`, which this repo does not vendor.
-/

namespace Soulgem
open Lean4Lean

def VExpr.false : VExpr := .forallE (.sort .zero) (.bvar 0)

def DefWF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

theorem addConst_constants {env env' : VEnv} {name : Name} {ci : VConstant}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

end Soulgem
