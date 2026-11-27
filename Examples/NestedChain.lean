import Examples.Checker.CheckNested
import Soulgem.Model.Admits
import Examples.Checker.CheckWF

/-! # Chains of checked plain and nested steps (`chainN_admits`) -/

namespace Soulgem.Examples
open Soulgem.Checker
open Lean4Lean Soulgem Soulgem.Spec

/-- A plain block, or a nested declaration with its translation's block. -/
inductive Step where
  | plain (b : SBlock)
  | nested (u : UDecl) (b : SBlock)

/-- One step, checked: the new environment and record, or `none`. -/
def Step.run (env : VEnv) (rec : List RBlock) : Step → Option (VEnv × List RBlock)
  | .plain b => if b.checkWF env then (b.add env).map (b.addEta ·, rec ++
      [RBlock.plain b]) else none
  | .nested u b =>
    match elim (indOf rec) (fun c => (env.constants c).isSome) u with
    | .ok tr =>
      let fams := familiesFor rec tr b u.types.length
      if nestedWFB tr b u.types.length rec env u fams then
        (addNested tr b u.types.length env).map
          (·, rec ++ [{ b, nuser := u.types.length, tr }])
      else none
    | .error _ => none

def chainN : VEnv → List RBlock → List Step → Option (VEnv × List RBlock)
  | env, rec, [] => some (env, rec)
  | env, rec, s :: ss => (s.run env rec).bind fun (env', rec') => chainN env' rec' ss

theorem Step.run_admits {base env : VEnv} {rec : List RBlock} {s : Step} {env' : VEnv}
    {rec' : List RBlock} (H : Admits base env rec) (h : s.run env rec = some (env', rec')) :
    Admits base env' rec' := by
  cases s with
  | plain b =>
    simp only [Step.run] at h
    split at h
    · rename_i hwf
      cases hadd : b.add env with
      | none => simp [hadd] at h
      | some e =>
        simp only [hadd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .plain H (b.checkWF_sound hwf) hadd
    · cases h
  | nested u b =>
    simp only [Step.run] at h
    split at h
    · rename_i tr he
      split at h
      · rename_i hwf
        cases hadd : addNested tr b u.types.length env with
        | none => simp [hadd] at h
        | some e =>
          simp only [hadd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have H' := Admits.nested H he (nestedWFB_sound tr b _ hwf) hadd
          rwa [addCertified_of_none tr b _ (nestedWFB_none tr b _ hwf)] at H'
      · cases h
    · cases h

theorem chainN_admits {base : VEnv} : ∀ {env : VEnv} {rec : List RBlock} (ss : List Step)
    {env' : VEnv} {rec' : List RBlock}, Admits base env rec → chainN env rec ss =
        some (env', rec') →
    Admits base env' rec'
  | env, rec, [], env', rec', H, h => by
    simp only [chainN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact H
  | env, rec, s :: ss, env', rec', H, h => by
    simp only [chainN] at h
    cases hs : s.run env rec with
    | none => simp [hs] at h
    | some p =>
      simp only [hs, Option.bind_some] at h
      exact chainN_admits ss (Step.run_admits H hs) h

/-- `chainN_admits` on the chain's result, so the elaborator never evaluates the chain. -/
theorem chainN_admits_get {base env : VEnv} {rec : List RBlock} {ss : List Step}
    (H : Admits base env rec) (h : (chainN env rec ss).isSome = true) :
    Admits base ((chainN env rec ss).get h).1 ((chainN env rec ss).get h).2 :=
  chainN_admits ss H (Option.some_get h).symm

end Soulgem.Examples
