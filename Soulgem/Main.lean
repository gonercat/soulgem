import Soulgem.Sound
import Soulgem.Base
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Extending a model by a single constant, and consistency from a model

Provides `Good`, `IsModel.addConst`, and `no_false_of_model`.
-/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean

universe u
variable {V : Type u} [SetTheory V]

/-! ## Which constants a term mentions -/

def ConstsIn (P : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const c _ => P c
  | .app f a | .lam f a | .forallE f a => ConstsIn P f ∧ ConstsIn P a

theorem ConstsIn.mono {P Q : Name → Prop} (h : ∀ c, P c → Q c) :
    ∀ {e : VExpr}, ConstsIn P e → ConstsIn Q e
  | .bvar _, _ | .sort _, _ => trivial
  | .const _ _, hc => h _ hc
  | .app .., hc | .lam .., hc | .forallE .., hc => ⟨hc.1.mono h, hc.2.mono h⟩

theorem constsIn_liftN {P : Name → Prop} {n : Nat} :
    ∀ {e : VExpr} {k : Nat}, ConstsIn P (e.liftN n k) ↔ ConstsIn P e
  | .bvar _, _ | .sort _, _ | .const _ _, _ => .rfl
  | .app .., _ | .lam .., _ | .forallE .., _ => by
    simp only [VExpr.liftN, ConstsIn, constsIn_liftN]

theorem ConstsIn.inst {P : Name → Prop} :
    ∀ {e : VExpr}, ConstsIn P e → ∀ {e' : VExpr}, ConstsIn P e' → ∀ {k : Nat},
      ConstsIn P (e.inst e' k)
  | .bvar i, _, _, h', k => by
    simp only [VExpr.inst, VExpr.instVar]
    split; · trivial
    split; · exact constsIn_liftN.mpr h'
    trivial
  | .sort _, h, _, _, _ | .const _ _, h, _, _, _ => h
  | .app .., h, _, h', _ | .lam .., h, _, h', _ | .forallE .., h, _, h', _ =>
    ⟨h.1.inst h', h.2.inst h'⟩

theorem constsIn_instL {P : Name → Prop} {ls : List VLevel} :
    ∀ {e : VExpr}, ConstsIn P (e.instL ls) ↔ ConstsIn P e
  | .bvar _ | .sort _ | .const _ _ => .rfl
  | .app .. | .lam .. | .forallE .. => by simp only [VExpr.instL, ConstsIn, constsIn_instL]

theorem interp_congr {M M' : CInterp V} {ls : List Nat} :
    ∀ {e : VExpr}, ConstsIn (fun c => M c = M' c) e → ∀ ρ, interp M ls e ρ = interp M' ls e ρ
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .const _ _, h, _ => by simp only [interp, show M _ = M' _ from h]
  | .app .., h, ρ => by simp only [interp, interp_congr h.1, interp_congr h.2]
  | .lam .., h, ρ => by simp only [interp, interp_congr h.1, interp_congr h.2]
  | .forallE .., h, ρ => by simp only [interp, interp_congr h.1, interp_congr h.2]

def Dom (env : VEnv) (c : Name) : Prop := env.constants c ≠ none

theorem Dom.mono {env env' : VEnv} (h : env ≤ env') {c} (hc : Dom env c) : Dom env' c := by
  unfold Dom at *
  cases e : env.constants c with
  | none => exact absurd e hc
  | some ci => rw [h.constants e]; simp

theorem Lookup.constsIn {P : Name → Prop} {Γ : List VExpr} {i A} (H : Lookup Γ i A)
    (hΓ : ∀ B ∈ Γ, ConstsIn P B) : ConstsIn P A := by
  induction H with
  | zero => exact constsIn_liftN.mpr (hΓ _ (.head _))
  | succ _ ih => exact constsIn_liftN.mpr (ih fun B hB => hΓ B (.tail _ hB))

theorem IsDefEq.constsIn {env : VEnv}
    (henv : env.OnTypes fun _ e A => ConstsIn (Dom env) e ∧ ConstsIn (Dom env) A)
    {U Γ e₁ e₂ A} (H : env.IsDefEq U Γ e₁ e₂ A) :
    (∀ B ∈ Γ, ConstsIn (Dom env) B) →
      ConstsIn (Dom env) e₁ ∧ ConstsIn (Dom env) e₂ ∧ ConstsIn (Dom env) A := by
  induction H with
  | bvar h => intro hΓ; exact ⟨trivial, trivial, Lookup.constsIn h hΓ⟩
  | symm _ ih => intro hΓ; have := ih hΓ; exact ⟨this.2.1, this.1, this.2.2⟩
  | trans _ _ ih1 ih2 => intro hΓ; exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | sortDF => intro; exact ⟨trivial, trivial, trivial⟩
  | constDF h1 =>
    intro
    obtain ⟨_, hT, -⟩ := henv.1 h1
    refine ⟨?_, ?_, constsIn_instL.mpr hT⟩ <;> (simp only [ConstsIn, Dom]; rw [h1]; simp)
  | appDF _ _ ih1 ih2 =>
    intro hΓ
    obtain ⟨hf, hf', -, hB⟩ := ih1 hΓ
    obtain ⟨ha, ha', -⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, hB.inst ha⟩
  | lamDF _ _ ih1 ih2 =>
    intro hΓ
    obtain ⟨hA, hA', -⟩ := ih1 hΓ
    obtain ⟨hb, hb', hB⟩ := ih2 (by
      intro B hB; cases hB with | head => exact hA | tail _ h => exact hΓ B h)
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, ⟨hA, hB⟩⟩
  | forallEDF _ _ ih1 ih2 =>
    intro hΓ
    obtain ⟨hA, hA', -⟩ := ih1 hΓ
    obtain ⟨hb, hb', -⟩ := ih2 (by
      intro B hB; cases hB with | head => exact hA | tail _ h => exact hΓ B h)
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 =>
    intro hΓ; exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    intro hΓ
    obtain ⟨he', -, hA⟩ := ih2 hΓ
    obtain ⟨he, -, hB⟩ := ih1 (by
      intro B hB; cases hB with | head => exact hA | tail _ h => exact hΓ B h)
    exact ⟨⟨⟨hA, he⟩, he'⟩, he.inst he', hB.inst he'⟩
  | eta _ ih =>
    intro hΓ
    obtain ⟨he, -, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, constsIn_liftN.mpr he, trivial⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    intro hΓ; exact ⟨(ih2 hΓ).1, (ih3 hΓ).1, (ih2 hΓ).2.2⟩
  | extra h1 =>
    intro
    obtain ⟨⟨hl, hT⟩, hr, -⟩ := henv.2 h1
    exact ⟨constsIn_instL.mpr hl, constsIn_instL.mpr hr, constsIn_instL.mpr hT⟩

/-! ## Building the model declaration by declaration -/

def Good (env : VEnv) : Prop :=
  env.OnTypes (fun _ e A => e.ClosedN ∧ A.ClosedN) ∧
  env.OnTypes (fun _ e A => ConstsIn (Dom env) e ∧ ConstsIn (Dom env) A)

theorem map_eval_params {ls : List Nat} {n : Nat} (h : ls.length = n) :
    (VLevel.params n).map (VLevel.eval ls) = ls := by
  subst h
  apply List.ext_getElem (by simp [VLevel.params])
  intro i h1 h2
  simp [VLevel.params, VLevel.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem IsModel.addConst {M : CInterp V} {env env' : VEnv} (hM : IsModel M env)
    (hG : Good env) {ci : VDefVal} (hci : DefWF env ci)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    let M' : CInterp V := fun c ls => if c = ci.name then interp M ls ci.value [] else M c ls
    IsModel M' env' ∧
      (∀ ls : List Nat, ls.length = ci.uvars → ∀ ρ,
        M' ci.name ls = interp M' ls ci.value ρ ∧ M' ci.name ls ∈ˢ interp M' ls ci.type ρ) ∧
      (∀ ls : List Nat, ls.length = ci.uvars → ∀ ρ,
        interp M' ls ci.toDefEq.lhs ρ = interp M' ls ci.toDefEq.rhs ρ ∧
        interp M' ls ci.toDefEq.lhs ρ ∈ˢ interp M' ls ci.toDefEq.type ρ) := by
  intro M'
  have hfresh : env.constants ci.name = none := by
    unfold VEnv.addConst at hadd; split at hadd <;> simp_all
  have hagree : ∀ e, ConstsIn (Dom env) e → ∀ ls ρ, interp M' ls e ρ = interp M ls e ρ :=
    fun e he ls ρ => interp_congr (he.mono fun c hc => by
      funext ls'; simp only [M']
      rw [ite_eq_right]; rintro rfl; exact hc hfresh) ρ
  have hCI := hG.2
  obtain ⟨hv, -, hT⟩ := IsDefEq.constsIn hCI hci nofun
  obtain ⟨hvc, -, hTc⟩ := hci.closedN' hG.1 trivial
  have hsound := fun ls => (hM.sound hci ls [] trivial).2
  have hnew : ∀ ls : List Nat, ls.length = ci.uvars → ∀ ρ,
      M' ci.name ls = interp M' ls ci.value ρ ∧ M' ci.name ls ∈ˢ interp M' ls ci.type ρ := by
    intro ls _ ρ
    have e1 : M' ci.name ls = interp M ls ci.value [] := ite_eq_left rfl
    rw [e1, hagree _ hv, hagree _ hT, interp_closed M ls hvc ρ, interp_closed M ls hTc ρ]
    exact ⟨rfl, hsound ls⟩
  refine ⟨⟨fun {c ci'} h ls hl ρ => ?_, fun {df} h ls hl ρ => ?_⟩, hnew, fun ls hl ρ => ?_⟩
  rotate_left 2
  · simp only [VDefVal.toDefEq, interp]
    rw [map_eval_params hl]
    exact hnew ls hl ρ
  · rw [addConst_constants hadd] at h
    simp only at h
    split at h
    · cases h; subst c; exact (hnew ls hl ρ).2
    · rename_i hne
      obtain ⟨_, hT', -⟩ := hCI.1 h
      have : M' c ls = M c ls := ite_eq_right (Ne.symm hne)
      rw [this, hagree _ hT']
      exact hM.const h ls hl ρ
  · have h' : env.defeqs df := by
      unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; exact h
    obtain ⟨⟨hl', hT'⟩, hr', -⟩ := hCI.2 h'
    rw [hagree _ hl', hagree _ hr', hagree _ hT']
    exact hM.defeq h' ls hl ρ

/-- An environment with a model proves no closed inhabitant of `∀ p : Prop, p`. -/
theorem no_false_of_model {M : CInterp V} {env : VEnv} (hM : IsModel M env) {U : Nat} :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  rintro ⟨e, he⟩
  have := (hM.sound he [] [] trivial).2
  simp only [interp, VExpr.false, VLevel.eval, List.getD_cons_zero] at this
  exact cpi_prop_id_empty this

end Soulgem
