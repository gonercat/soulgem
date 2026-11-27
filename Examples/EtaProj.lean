import Examples.Checker.CheckWF
import Checks.KReduce
import Examples.Blocks
import Soulgem.CoreModel
import Soulgem.Spec.Env
import Soulgem.Extend

/-! # Structure eta through the projections `Prod.fst` and `Prod.snd`, admitted -/

namespace Soulgem.Examples
open Lean4Lean Soulgem Soulgem.Spec

/-- `A` beta-reduces to `B` in one step, with a type body. -/
def betaB (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Bool
  | .app (.lam T b) x, e =>
    decide (b.inst x = e) && Checks.isTypeB env U (T :: Γ) b &&
      decide (Checks.infer env U Γ x = some T)
  | _, _ => false

theorem betaB_sound {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {A B : VExpr}, betaB env U Γ A B = true → ∃ u, env.IsDefEq U Γ A B (.sort u)
  | .app (.lam _ _) _, _, h => by
    simp only [betaB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hb⟩, hx⟩ := h
    obtain ⟨u, hu⟩ := Checks.isTypeB_sound hb
    exact ⟨u, .beta hu (Checks.infer_sound hx)⟩
  | .bvar _, _, h | .sort _, _, h | .const _ _, _, h | .lam _ _, _, h | .forallE _ _, _, h
  | .app (.bvar _) _, _, h | .app (.sort _) _, _, h | .app (.const _ _) _, _, h
  | .app (.app _ _) _, _, h | .app (.forallE _ _) _, _, h => by simp [betaB] at h

/-- Equal types: syntax, one beta step, or `forallE` congruence. -/
def convB (env : VEnv) (U : Nat) : List VExpr → VExpr → VExpr → Bool
  | Γ, A, B =>
    (decide (A = B) && Checks.isTypeB env U Γ A) || betaB env U Γ A B || betaB env U Γ B A ||
    match A, B with
    | .forallE A B, .forallE A' B' =>
      decide (A = A') && Checks.isTypeB env U Γ A && convB env U (A :: Γ) B B'
    | _, _ => false

theorem convB_sound {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr} {A B : VExpr}, convB env U Γ A B = true → ∃ u, env.IsDefEq U Γ A B (.sort u)
  | Γ, A, B, h => by
    unfold convB at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, hA⟩ | h) | h) | h
    · exact Checks.isTypeB_sound hA
    · exact betaB_sound h
    · obtain ⟨u, hu⟩ := betaB_sound h; exact ⟨u, hu.symm⟩
    · split at h
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, hA⟩, hB⟩ := h
        obtain ⟨u, hu⟩ := Checks.isTypeB_sound hA
        obtain ⟨v, hv⟩ := convB_sound hB
        exact ⟨_, .forallEDF hu hv⟩
      · cases h

/-- `Checks.infer`, comparing argument types with domains by `convB`. -/
def inferC (env : VEnv) (U : Nat) : List VExpr → VExpr → Option VExpr
  | Γ, .app f a =>
    match inferC env U Γ f, inferC env U Γ a with
    | some (.forallE A B), some A' => if convB env U Γ A' A then some (B.inst a) else none
    | _, _ => none
  | Γ, .lam A b =>
    match Checks.infer env U Γ A, inferC env U (A :: Γ) b with
    | some (.sort _), some B => some (.forallE A B)
    | _, _ => none
  | Γ, .bvar i => Checks.infer env U Γ (.bvar i)
  | Γ, .sort u => Checks.infer env U Γ (.sort u)
  | Γ, .const c ls => Checks.infer env U Γ (.const c ls)
  | Γ, .forallE A B => Checks.infer env U Γ (.forallE A B)

theorem inferC_sound {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr} {e A : VExpr}, inferC env U Γ e = some A → env.HasType U Γ e A
  | _, .app _ _, _, h => by
    unfold inferC at h
    split at h
    · next hf ha =>
      split at h
      · next hc =>
        cases h
        obtain ⟨_, hu⟩ := convB_sound hc
        exact VEnv.HasType.app (inferC_sound hf) (.defeqDF hu (inferC_sound ha))
      · cases h
    · cases h
  | _, .lam _ _, _, h => by
    unfold inferC at h
    split at h
    · next hA hb => cases h; exact VEnv.HasType.lam (Checks.infer_sound hA) (inferC_sound hb)
    · cases h
  | _, .bvar _, _, h | _, .sort _, _, h | _, .const _ _, _, h | _, .forallE _ _, _, h => by
    unfold inferC at h; exact Checks.infer_sound h

def hasTypeCB (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Bool :=
  match inferC env U Γ e with
  | some A' => convB env U Γ A' A
  | none => false

theorem hasTypeCB_sound {env : VEnv} {U : Nat} {Γ : List VExpr} {e A : VExpr}
    (h : hasTypeCB env U Γ e A = true) : env.HasType U Γ e A := by
  unfold hasTypeCB at h
  split at h
  · next he => obtain ⟨_, hu⟩ := convB_sound h; exact .defeqDF hu (inferC_sound he)
  · cases h


theorem prod_add_isSome : (Prod_block.add Core.coreEnv).isSome = true := by decide +kernel

/-- `Prod` over the core logic, with its eta rule. -/
def prodEnv : VEnv := Prod_block.addEta ((Prod_block.add Core.coreEnv).get prod_add_isSome)

theorem prod_admitted : Admits Core.coreEnv prodEnv [RBlock.plain Prod_block] :=
  .plain .base (Prod_block.checkWF_sound (by decide +kernel))
    (Option.eq_some_of_isSome prod_add_isSome)

theorem prod_etaRule_isSome : Prod_block.etaRule.isSome = true := by decide +kernel

theorem prod_etaCtor_isSome : Prod_block.etaCtor?.isSome = true := by decide +kernel

def prodMk : SCtor := Prod_block.etaCtor?.get prod_etaCtor_isSome

def prodNames : List Name := [`Prod.fst, `Prod.snd]

def prodNm : Nat → Name := (prodNames.getD · .anonymous)

def fstDef : VDefVal := Prod_block.projDefVal `Prod.fst prodNm prodMk 0

def sndDef : VDefVal := Prod_block.projDefVal `Prod.snd prodNm prodMk 1

/-- Control: the projection's value has no type without conversion. -/
theorem fst_infer_none : Checks.infer prodEnv 2 [] fstDef.value = none := by decide +kernel

theorem fst_wf : DefWF prodEnv fstDef := hasTypeCB_sound (by decide +kernel)

theorem fst_add_isSome : (prodEnv.addConst fstDef.name fstDef.toVConstant).isSome = true := by
  decide +kernel

def fstEnv : VEnv :=
  ((prodEnv.addConst fstDef.name fstDef.toVConstant).get fst_add_isSome).addDefEq fstDef.toDefEq

theorem snd_wf : DefWF fstEnv sndDef := hasTypeCB_sound (by decide +kernel)

theorem snd_add_isSome : (fstEnv.addConst sndDef.name sndDef.toVConstant).isSome = true := by
  decide +kernel

def sndEnv : VEnv :=
  ((fstEnv.addConst sndDef.name sndDef.toVConstant).get snd_add_isSome).addDefEq sndDef.toDefEq

theorem snd_admitted : Admits Core.coreEnv sndEnv [RBlock.plain Prod_block] :=
  .def (.def prod_admitted fst_wf (Option.eq_some_of_isSome fst_add_isSome)) snd_wf
    (Option.eq_some_of_isSome snd_add_isSome)

deriving instance DecidableEq for VConstant

theorem sndEnv_constants : ∀ i < prodNames.length, sndEnv.constants (prodNames.getD i .anonymous) =
    some ⟨Prod_block.uvars, Prod_block.projTyP prodNm prodMk i⟩ := by
  decide +kernel

theorem sndEnv_defeqs : ∀ i < prodNames.length, (prodMk.fields[i]!).sort.isAlwaysZero = false →
    sndEnv.defeqs (Prod_block.projDefVal (prodNames.getD i .anonymous) prodNm prodMk i).toDefEq
  | 0, _, _ => .inr (by
      rw [addConst_defeqs (Option.eq_some_of_isSome snd_add_isSome)]; exact .inl rfl)
  | 1, _, _ => .inl rfl
  | _ + 2, h, _ => by simp only [prodNames, List.length_cons, List.length_nil] at h; omega

/-- `Prod`, its projections and the eta rule written with them, admitted. -/
theorem prod_etaProj_admitted :
    Admits Core.coreEnv (sndEnv.addDefEq (Prod_block.etaRuleP prodNm prodMk))
      [RBlock.plain Prod_block] :=
  .etaProj snd_admitted (List.mem_singleton.mpr rfl) (Option.eq_some_of_isSome prod_etaCtor_isSome)
    (by decide +kernel) sndEnv_constants sndEnv_defeqs

end Soulgem.Examples
