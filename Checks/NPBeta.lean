import Checks.KDerive
import Lean.Util.CollectAxioms
/-! # Spec admits `NPBeta := mk (f : ∀ x : (fun _ : Type => Nat) NPBeta, NPBeta)`; rc3 refuses it

The kernel's positivity check reads the field's binder domain without reducing it; Spec's `FieldOK`
asks only that the field be definitionally equal to `∀ x : Nat, NPBeta`.
-/
namespace Soulgem.Checks.NPBetaProbe
open Lean Lean4Lean Soulgem Soulgem.Spec

def np : VExpr := .const `NPBeta []
def nat : VExpr := .const `Nat []
def dom : VExpr := .app (.lam (.sort (.succ .zero)) nat) np
def fty : VExpr := .forallE dom np

def npMk : SCtor where
  name := `NPBeta.mk
  type := .forallE fty np
  fields := [{ ty := fty, sort := .imax (.succ .zero) (.succ .zero), cert := .recursive [nat] 0 [] }]
  idx := []

def npBlock : SBlock where
  uvars := 0
  params := []
  level := .succ .zero
  types := [{ name := `NPBeta, type := .sort (.succ .zero), indices := [], ctors := [npMk] }]

theorem np_withTypes_isSome : (npBlock.withTypes envN).isSome = true := by decide

def e₁ : VEnv := (npBlock.withTypes envN).get np_withTypes_isSome

theorem hNP (Γ : List VExpr) (h : infer e₁ 0 Γ np = some (.sort (.succ .zero)) := by decide) :
    e₁.HasType 0 Γ np (.sort (.succ .zero)) :=
  infer_sound h

theorem hNat (Γ : List VExpr) (h : infer e₁ 0 Γ nat = some (.sort (.succ .zero)) := by decide) :
    e₁.HasType 0 Γ nat (.sort (.succ .zero)) :=
  infer_sound h

/-- The field is `∀ x : Nat, NPBeta` up to one beta step in the binder domain. -/
theorem field_defEq : DefEqTy e₁ 0 [] fty (.forallE nat np) := by
  have hb : e₁.IsDefEq 0 [] dom nat (.sort (.succ .zero)) :=
    .beta (hNat [.sort (.succ .zero)]) (hNP [])
  exact ⟨_, .forallEDF hb (hNP [dom])⟩

theorem npBlock_WF : npBlock.WF envN := by
  have hj (j : Nat) (hj : j < npBlock.ntypes) : j = 0 := by
    simp [npBlock, SBlock.ntypes] at hj; omega
  have hc (c : SCtor) (hc : c ∈ (npBlock.types[0]!).ctors) : c = npMk := by
    simpa [npBlock] using hc
  refine ⟨⟨List.cons_ne_nil _ _, by decide, ?_⟩, by decide, ?_, ?_, ?_⟩
  · intro j hj' c hc'
    obtain rfl := hj j hj'; obtain rfl := hc c hc'
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro f hf
    simp only [npMk, List.mem_singleton] at hf; subst hf
    simp only [SBlock.FieldSyn]; decide
  · intro i hi; simp [npBlock, SBlock.nparams] at hi
  · intro t ht
    simp only [npBlock, List.mem_singleton] at ht; subst ht
    exact ⟨fun a ha => by simp at ha, defEqTyB_sound (by decide)⟩
  · refine ⟨_, Option.eq_some_of_isSome np_withTypes_isSome, ?_⟩
    intro j hj' c hc'
    obtain rfl := hj j hj'; obtain rfl := hc c hc'
    refine ⟨isTypeB_sound (by decide), fun i h => by simp [npBlock, SBlock.nparams] at h,
      fun l h => by simp [npMk] at h, fun a ha => ?_⟩
    have ha0 : a = 0 := by simpa [npMk] using ha
    subst ha0
    have hfc : npBlock.fieldCtx npMk 0 = [] := by decide
    refine ⟨?_, ?_, .inr fun ls => by simp [npMk, npBlock, VLevel.eval, Lean.Nat.imax], ?_⟩
    · rw [hfc]; exact hasTypeB_sound (by decide)
    · rw [hfc]; exact annB_sound (by decide)
    · rw [hfc]
      show DefEqTy e₁ 0 [] fty _ ∧ _
      refine ⟨field_defEq, fun e he => ?_, fun l hl => by simp at hl, fun e he => ?_⟩
      · have he0 : e = 0 := by simpa using he
        subst he0; exact annB_sound (by decide)
      · have he0 : e = 0 := by simpa using he
        subst he0
        exact ⟨.succ .zero, hNat [], fun _ _ => Nat.le_refl _⟩

theorem np_add_isSome : (npBlock.add envN).isSome = true := by decide

/-- Spec admits core, then `Nat`, then `NPBeta`. -/
theorem np_admitted : ∃ env, Admits Core.coreEnv env [.plain Nested.natBlock, .plain npBlock] :=
  ⟨_, .plain (.plain .base Nested.natBlock_WF (Option.eq_some_of_isSome nat_add_isSome))
    npBlock_WF (Option.eq_some_of_isSome np_add_isSome)⟩

end Soulgem.Checks.NPBetaProbe

open Lean in
set_option Elab.async false in
#eval show MetaM Unit from do
  let nat := Expr.const ``Nat []
  let decl (nm : Name) (dom : Expr → Expr) : Expr × Declaration :=
    let I := Expr.const nm []
    let cty := Expr.forallE `f (.forallE `x (dom I) I .default) I .default
    let c : Constructor := { name := nm ++ `mk, type := cty }
    let t : InductiveType := { name := nm, type := .sort (.succ .zero), ctors := [c] }
    (cty, .inductDecl [] 0 [t] false)
  let (cty, d) := decl `NPBeta fun I => .app (.lam `y (.sort (.succ .zero)) nat .default) I
  let v ← Lean4Lean.Meta.ofExpr [] {} cty
  unless toExpr v == toExpr Soulgem.Checks.NPBetaProbe.npMk.type do
    throwError "NPBeta.mk differs from npMk under ofExpr"
  for (nm, want, d) in [("NPControl", true, (decl `NPControl fun _ => nat).2), ("NPBeta", false, d)] do
    let r ← try addDecl d; pure none catch e => pure (some (← e.toMessageData.toString))
    IO.println s!"positivity {nm}: {if r.isNone then "accepted" else "refused"}"
    unless r.isNone == want do throwError "positivity {nm}: expected {if want then "accepted" else "refused"}"
  let axs ← collectAxioms ``Soulgem.Checks.NPBetaProbe.np_admitted
  IO.println s!"np_admitted: {axs.toList}"
  for a in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "np_admitted depends on axiom {a}"
