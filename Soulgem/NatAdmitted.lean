import Soulgem.CoreModel
import Soulgem.NatBlock
import Soulgem.Spec.Env
/-! # `Spec.Admits` admits the block `natBlock` -/
namespace Soulgem.Nested
open Lean4Lean Spec

theorem natBlock_WF : natBlock.WF Core.coreEnv := by
  have hT : Core.coreEnv.HasType 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sortDF trivial trivial (funext fun _ => rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [natBlock], by decide, ?_⟩
    intro j hj c hc
    have hj0 : j = 0 := by simp [natBlock, SBlock.ntypes] at hj; omega
    subst hj0
    simp only [natBlock, List.getElem!_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨by decide, by decide, by decide, by decide, by simp⟩
    · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
      intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
      exact ⟨by decide, by decide, by simp, by simp⟩
  · trivial
  · intro i hi; simp [natBlock, SBlock.nparams] at hi
  · intro t ht
    simp only [natBlock, List.mem_cons, List.not_mem_nil, or_false] at ht; subst ht
    exact ⟨fun a ha => by simp at ha, ⟨.succ (.succ .zero), hT⟩⟩
  · let e1 : VEnv := { Core.coreEnv with
      constants := fun n => if `Nat = n then some ⟨0, .sort (.succ
          .zero)⟩ else Core.coreEnv.constants n }
    have hwt : natBlock.withTypes Core.coreEnv = some e1 := by
      simp [e1, SBlock.withTypes, natBlock, VEnv.addConst, Core.coreEnv, Core.lookupC,
          Core.coreConsts]
    refine ⟨_, hwt, ?_⟩
    intro j hj c hc
    have hj0 : j = 0 := by simp [natBlock, SBlock.ntypes] at hj; omega
    subst hj0
    have hNat (Γ : List VExpr) : e1.HasType 0 Γ (.const `Nat []) (.sort (.succ .zero)) := by
      simpa [VEnv.HasType, VExpr.instL, VLevel.inst] using
        VEnv.IsDefEq.constDF (env := e1) (uvars := 0) (Γ := Γ) (c := `Nat)
            (ci := ⟨0, .sort (.succ .zero)⟩)
          (by simp [e1]) (by simp) (by simp) rfl .nil
    simp only [natBlock, List.getElem!_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨⟨_, hNat []⟩, fun i hi => by
        simp [natBlock, SBlock.nparams] at hi, fun l hl => by simp at hl,
        fun a ha => by simp at ha⟩
    · refine ⟨⟨_, .forallEDF (hNat []) (hNat _)⟩, fun i hi => by
        simp [natBlock, SBlock.nparams] at hi,
        fun l hl => by simp at hl, ?_⟩
      intro a ha
      have ha0 : a = 0 := by simp at ha; omega
      subst ha0
      exact ⟨hNat [], ⟨_, hNat []⟩, Or.inr (fun _ => Nat.le_refl _),
        ⟨⟨_, hNat []⟩, fun e he => by
            simp at he, fun l hl => by simp at hl, fun e he => by simp at he⟩⟩

theorem natBlock_admitted : ∃ env, Admits Core.coreEnv env [RBlock.plain natBlock] := by
  have hadd : ∃ env', natBlock.add Core.coreEnv = some env' := by
    unfold SBlock.add
    simp [SBlock.withTypes, SBlock.ctors, SBlock.ntypes, SBlock.recName, SBlock.recUvars,
        SBlock.recType,
      natBlock, VEnv.addConst, Core.coreEnv, Core.lookupC, Core.coreConsts]
  obtain ⟨env', hadd⟩ := hadd
  exact ⟨_, Admits.plain Admits.base natBlock_WF hadd⟩

end Soulgem.Nested
